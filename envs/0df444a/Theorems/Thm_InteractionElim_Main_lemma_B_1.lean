-- Prove2me | Theorems.Thm_InteractionElim_Main_lemma_B_1
-- name    : InteractionElim.Main.lemma_B_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:21:48.203209+00:00
-- url     : https://prove2.me/theorems/ce77a123-ffea-48af-980e-d673b4c7b024
-- title:
--   Lemma B.1 — residual-kernel converse $K\ge\frac{wL}{2\ln7}T_{\ker}$, and $\tau(0,W^\perp)\le F(W)\le G(W)\le\dim W+\tau(0,W^\perp)$
-- statement:
--   Fix a workflow instance ($R\ge16$) with $L=\ln(1/\delta)\ge\ln(R+1)$. Every reliable admissible protocol whose worst-world fee $K$ is finite satisfies
--   $$
--   K\ge\frac{wL}{2\ln7}\,T_{\ker},\qquad T_{\ker}=\sum_j\tau(0,W_j^\perp), \tag{B.6}
--   $$
--   and in particular $wL\ge\gamma/2$ implies $K\ge\gamma T_{\ker}/(4\ln7)$. For every subspace (stage space) $W\le\mathbb F_2^r$,
--   $$
--   \tau(0,W^\perp)\le F(W)\le G(W)\le\dim W+\tau(0,W^\perp), \tag{B.7}
--   $$
--   and consequently, for every instance, $T_{\ker}\le\Phi\le\sum_jG(W_j)\le\operatorname{rank}A+T_{\ker}$.
--
--   $T_{\ker}$ is experimental work that remains even when the whole expert record is revealed for free; the lemma prices it for every ongoing protocol.
--
--   Differences from the source:
--   - encoding: coordinates [R] = {1,…,R}, ordered blocks B_1,…,B_m, x ∈ F_2^R → `Fin R`, a surjective block map `Fin R → Fin m` (0-based stage order), vectors `Fin R → ZMod 2`; reason: index shift only; every ordered partition into nonempty blocks is such a surjection
--   - reading: §2 (p. 4) describes protocols in prose: a public parser, an expert whose bits depend only on Ax, the public history and its tape, an agent with private current-block queries that may preempt the expert by a submission, private abandonment, independent private tapes → `Protocol`/`step`/`run`: deterministic strategies of fair-coin tapes and views; the expert's abandonment is decided at every newly reached public history; an illegal move (query outside the current block, a paid bit out of turn, yielding when the expert is not designated) is abandonment; strategies are measurable in their tapes; reason: the source gives the model only in prose; this reading keeps every constraint of p. 4 (no shared tape, no free symbol, no clock), fair-coin tapes simulate any private randomization, and measurability is the standing convention that makes the execution law defined
--   - encoding: the fee (2.1) and the values C_ad, C_pre, C_lin as infima of fees → fees, C_ad, C_pre, C_lin in ℝ≥0∞ (lower integral of the path cost, supremum over worlds, infimum over the class); reason: (2.2)'s remark allows infinite-fee protocols; every finite value is the same real number
--   - generalization: 'every stage space W ≤ F_2^r' in (B.7) → every subspace W of every F_2^r; reason: every positive-dimensional ambient space and subspace W is realized by a stage, padding other coordinates to R ≥ 16 if needed; the additional r = 0 case states 0 ≤ 0 ≤ 0 ≤ 0
--   - reading: 'every reliable admissible ongoing protocol' → every reliable admissible `Protocol` (ongoing = no restriction on when bits are exchanged); reason: 'ongoing' names the unrestricted class of C_ad
-- source:
--   Jin, Zang, Xu, Li, Eliminating Ongoing Interaction in Long-Running Verification Agents, STOC 2027 submission (manuscript sha256 44f6d829…), p. 23, Lemma B.1, Eqs. (B.6)-(B.7)

import Mathlib
import Definitions.Def_InteractionElim_Main_Protocol

open scoped BigOperators ENNReal
open MeasureTheory Matrix

namespace InteractionElim.Main

theorem lemma_B_1 :
    (∀ I : Instance, Real.log ((I.R : ℝ) + 1) ≤ I.L →
      ∀ pr : Protocol I, Reliable pr → Admissible pr → fee pr ≠ ⊤ →
        ENNReal.ofReal ((I.w : ℝ) * I.L / (2 * Real.log 7) * I.Tker) ≤ fee pr ∧
        ((I.γ : ℝ) / 2 ≤ (I.w : ℝ) * I.L →
          ENNReal.ofReal ((I.γ : ℝ) * I.Tker / (4 * Real.log 7)) ≤ fee pr)) ∧
    (∀ (r : ℕ) (W : Submodule (ZMod 2) (Fin r → ZMod 2)),
      tau 0 (orth W : Set (Fin r → ZMod 2)) ≤ F W ∧ F W ≤ G W ∧
        G W ≤ (Module.finrank (ZMod 2) W : ℝ) + tau 0 (orth W : Set (Fin r → ZMod 2))) ∧
    (∀ I : Instance, I.Tker ≤ I.Φ ∧ I.Φ ≤ I.sumG ∧ I.sumG ≤ (I.A.rank : ℝ) + I.Tker) := by sorry

end InteractionElim.Main
