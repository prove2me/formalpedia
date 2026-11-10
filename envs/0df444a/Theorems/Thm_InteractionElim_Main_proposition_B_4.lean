-- Prove2me | Theorems.Thm_InteractionElim_Main_proposition_B_4
-- name    : InteractionElim.Main.proposition_B_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:21:54.834212+00:00
-- url     : https://prove2.me/theorems/55195fbd-7d72-44d7-b44c-ebd648a6fb39
-- title:
--   Proposition B.4 — $\gamma\sum_jF(W_j)\le A K$ for every admissible interactive protocol of worst-world fee $K$
-- statement:
--   There is a universal constant $A>0$ such that, for every workflow instance in the regime (2.8), every admissible interactive protocol of worst-world fee $K$ satisfies
--   $$
--   \gamma\sum_jF(W_j)\le A K. \tag{B.34}
--   $$
--   The statement is formalized as printed: it quantifies over admissible protocols, without the word "reliable". It combines Propositions B.3 and B.6 into the lower half of (3.1) on the full regime.
--
--   **Formalization Note** $K$ is the fee in $[0,\infty]$; an infinite fee makes the inequality immediate.
--
--   Differences from the source:
--   - encoding: coordinates [R] = {1,…,R}, ordered blocks B_1,…,B_m, x ∈ F_2^R → `Fin R`, a surjective block map `Fin R → Fin m` (0-based stage order), vectors `Fin R → ZMod 2`; reason: index shift only; every ordered partition into nonempty blocks is such a surjection
--   - reading: §2 (p. 4) describes protocols in prose: a public parser, an expert whose bits depend only on Ax, the public history and its tape, an agent with private current-block queries that may preempt the expert by a submission, private abandonment, independent private tapes → `Protocol`/`step`/`run`: deterministic strategies of fair-coin tapes and views; the expert's abandonment is decided at every newly reached public history; an illegal move (query outside the current block, a paid bit out of turn, yielding when the expert is not designated) is abandonment; strategies are measurable in their tapes; reason: the source gives the model only in prose; this reading keeps every constraint of p. 4 (no shared tape, no free symbol, no clock), fair-coin tapes simulate any private randomization, and measurability is the standing convention that makes the execution law defined
--   - encoding: the fee (2.1) and the values C_ad, C_pre, C_lin as infima of fees → fees, C_ad, C_pre, C_lin in ℝ≥0∞ (lower integral of the path cost, supremum over worlds, infimum over the class); reason: (2.2)'s remark allows infinite-fee protocols; every finite value is the same real number
--   - encoding: universal constants, O(·) and ≍ → explicit existentially quantified positive real constants, quantified before every instance-dependent object; reason: the notation convention of p. 4: a ≍ b means two inequalities with positive universal constants
--   - reading: the standing assumption (2.8) of all protocol-fee results ('Unless a statement explicitly specifies otherwise', p. 5) → hypothesis `I.Regime`; reason: the statement does not specify otherwise, so (2.8) applies
-- source:
--   Jin, Zang, Xu, Li, Eliminating Ongoing Interaction in Long-Running Verification Agents, STOC 2027 submission (manuscript sha256 44f6d829…), p. 28, Proposition B.4, Eq. (B.34)

import Mathlib
import Definitions.Def_InteractionElim_Main_Protocol

open scoped BigOperators ENNReal
open MeasureTheory Matrix

namespace InteractionElim.Main

theorem proposition_B_4 :
    ∃ A : ℝ, 0 < A ∧ ∀ I : Instance, I.Regime → ∀ pr : Protocol I, Admissible pr →
      ENNReal.ofReal ((I.γ : ℝ) * I.Φ) ≤ ENNReal.ofReal A * fee pr := by sorry

end InteractionElim.Main
