-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_PhaseParameterAlignment_align_s238r
-- name    : OAI.MetricKMedianRecovery.PhaseParameterAlignment.align_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:35:32.934826+00:00
-- url     : https://prove2.me/theorems/29155ade-c11a-45be-84b7-a948c7e3a1e8
-- title:
--   OAI.MetricKMedianRecovery.PhaseParameterAlignment.align_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.PhaseParameterAlignment.align` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/RegularMap.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/RegularMap.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.PhaseParameterAlignment`, with `open PhaseSequence PhaseMergeCompletion PhaseCountCrossing`):
--
--   ```lean
--   theorem align_s238r (loc : D → X) (F B Q : Finset X) (G : List X) (r : X → X)
--       (v lam lam' eta eps : ℝ) (q n k a b : ℕ)
--       (hv : 0 < v) (hvsmall : v < 1/6) (hlam : 0 < lam) (heps : 0 ≤ eps)
--       (hprice : lam ≤ lam')
--       (herror : lam'-lam+(Fintype.card D:ℝ)*((1-3*v)*eps) ≤ (Fintype.card D:ℝ)*eta)
--       (hinj : Function.Injective r) (hfix : ∀ i ∈ F, r i = i)
--       (hQ : Q ⊆ F ∪ B)
--       (hshrink : ∀ j, ∀ x ∈ F ∪ B, dist (loc j) (r x) ≤ dist (loc j) x)
--       (hloss : ∀ j, ∀ x ∈ F ∪ B, dist (loc j) x ≤ dist (loc j) (r x)+eps)
--       (hrow : ∀ i ∈ F, bidRow loc (1-3*v) ((1+v^2)^q) Q i ≤ lam)
--       (hG : Valid loc F B Q v ((1+v^2)^q) lam 0 G)
--       (hGr : ∀ i ∈ G, i ∈ F) (hab : Sandwich k a b) :
--       Valid loc F (B.image r) (Q.image r) v ((1+v^2)^q) lam' eta G ∧
--         ∃ c, Attains loc F (B.image r) (Q.image r ∪ G.toFinset) v lam' (q+1) n c ∧
--           (c = k ∨ Sandwich k a c ∨ Sandwich k c b)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.bidRow` (definitions bundle `Q238L000` of this split); `OAI.MetricKMedianRecovery.PhaseCountCrossing.Sandwich` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.PhaseMergeCompletion.Attains` and `OAI.MetricKMedianRecovery.PhaseSequence.Valid` (definitions bundle `Q238L020` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.run_pack_s238r` and `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.step_correct_s238r` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/RegularMap.lean (declaration OAI.MetricKMedianRecovery.PhaseParameterAlignment.align)

import Mathlib
import Definitions.Def_Q238L020

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseParameterAlignment
open PhaseSequence PhaseMergeCompletion PhaseCountCrossing
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

theorem align_s238r (loc : D → X) (F B Q : Finset X) (G : List X) (r : X → X)
    (v lam lam' eta eps : ℝ) (q n k a b : ℕ)
    (hv : 0 < v) (hvsmall : v < 1/6) (hlam : 0 < lam) (heps : 0 ≤ eps)
    (hprice : lam ≤ lam')
    (herror : lam'-lam+(Fintype.card D:ℝ)*((1-3*v)*eps) ≤ (Fintype.card D:ℝ)*eta)
    (hinj : Function.Injective r) (hfix : ∀ i ∈ F, r i = i)
    (hQ : Q ⊆ F ∪ B)
    (hshrink : ∀ j, ∀ x ∈ F ∪ B, dist (loc j) (r x) ≤ dist (loc j) x)
    (hloss : ∀ j, ∀ x ∈ F ∪ B, dist (loc j) x ≤ dist (loc j) (r x)+eps)
    (hrow : ∀ i ∈ F, bidRow loc (1-3*v) ((1+v^2)^q) Q i ≤ lam)
    (hG : Valid loc F B Q v ((1+v^2)^q) lam 0 G)
    (hGr : ∀ i ∈ G, i ∈ F) (hab : Sandwich k a b) :
    Valid loc F (B.image r) (Q.image r) v ((1+v^2)^q) lam' eta G ∧
      ∃ c, Attains loc F (B.image r) (Q.image r ∪ G.toFinset) v lam' (q+1) n c ∧
        (c = k ∨ Sandwich k a c ∨ Sandwich k c b) := by
  sorry

end MetricKMedianRecovery.PhaseParameterAlignment

end OAI
end
