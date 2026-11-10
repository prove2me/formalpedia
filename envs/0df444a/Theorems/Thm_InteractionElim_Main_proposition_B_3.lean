-- Prove2me | Theorems.Thm_InteractionElim_Main_proposition_B_3
-- name    : InteractionElim.Main.proposition_B_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:21:56.494901+00:00
-- url     : https://prove2.me/theorems/6883a0ed-4388-4c1d-b7b5-d6d4918e1a82
-- title:
--   Proposition B.3 — interactive converse $K\ge2^{-14}\gamma\Phi$ without a nullity threshold
-- statement:
--   Fix a workflow instance ($R\ge16$) with
--   $$
--   wL\ge\gamma/2,\qquad L\ge\ln(R+1),\qquad \Phi\le L+2T_{\ker},\qquad \Phi=\sum_jF(W_j). \tag{B.17}
--   $$
--   Every reliable admissible protocol of finite worst-world fee $K$ satisfies
--   $$
--   K\ge2^{-14}\gamma\Phi. \tag{B.18}
--   $$
--   This is the lower half of (3.1) on the geometric branch of (2.8).
--
--   Differences from the source:
--   - encoding: coordinates [R] = {1,…,R}, ordered blocks B_1,…,B_m, x ∈ F_2^R → `Fin R`, a surjective block map `Fin R → Fin m` (0-based stage order), vectors `Fin R → ZMod 2`; reason: index shift only; every ordered partition into nonempty blocks is such a surjection
--   - reading: §2 (p. 4) describes protocols in prose: a public parser, an expert whose bits depend only on Ax, the public history and its tape, an agent with private current-block queries that may preempt the expert by a submission, private abandonment, independent private tapes → `Protocol`/`step`/`run`: deterministic strategies of fair-coin tapes and views; the expert's abandonment is decided at every newly reached public history; an illegal move (query outside the current block, a paid bit out of turn, yielding when the expert is not designated) is abandonment; strategies are measurable in their tapes; reason: the source gives the model only in prose; this reading keeps every constraint of p. 4 (no shared tape, no free symbol, no clock), fair-coin tapes simulate any private randomization, and measurability is the standing convention that makes the execution law defined
--   - encoding: the fee (2.1) and the values C_ad, C_pre, C_lin as infima of fees → fees, C_ad, C_pre, C_lin in ℝ≥0∞ (lower integral of the path cost, supremum over worlds, infimum over the class); reason: (2.2)'s remark allows infinite-fee protocols; every finite value is the same real number
--   - reading: 'every reliable admissible ongoing protocol' → every reliable admissible `Protocol`; reason: 'ongoing' names the unrestricted class of C_ad
-- source:
--   Jin, Zang, Xu, Li, Eliminating Ongoing Interaction in Long-Running Verification Agents, STOC 2027 submission (manuscript sha256 44f6d829…), p. 26, Proposition B.3, Eqs. (B.17)-(B.18)

import Mathlib
import Definitions.Def_InteractionElim_Main_Protocol

open scoped BigOperators ENNReal
open MeasureTheory Matrix

namespace InteractionElim.Main

theorem proposition_B_3 (I : Instance) (hwL : (I.γ : ℝ) / 2 ≤ (I.w : ℝ) * I.L)
    (hL : Real.log ((I.R : ℝ) + 1) ≤ I.L) (hΦ : I.Φ ≤ I.L + 2 * I.Tker)
    (pr : Protocol I) (hrel : Reliable pr) (hadm : Admissible pr) (hfee : fee pr ≠ ⊤) :
    ENNReal.ofReal ((2 : ℝ) ^ (-14 : ℤ) * I.γ * I.Φ) ≤ fee pr := by sorry

end InteractionElim.Main
