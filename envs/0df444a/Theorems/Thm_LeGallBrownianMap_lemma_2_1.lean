-- Prove2me | Theorems.Thm_LeGallBrownianMap_lemma_2_1
-- name    : LeGallBrownianMap.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:38:02.532415+00:00
-- url     : https://prove2.me/theorems/74ea98cb-0674-49ca-b8a4-697b8dca4d19
-- title:
--   Lemma 2.1 — increase times of $e$ are not increase times of $Z$
-- statement:
--   Let $e$ be a normalized Brownian excursion and $Z$ Brownian labels given $e$. With probability one, every $t\in[0,1]$ that is a right-increase time or a left-increase time of $e$ is neither a right-increase time nor a left-increase time of $Z$.
--
--   Combined with the description of leaves of the CRT, this shows that the hitting times $S_r$ of the labels project to leaves of $\mathcal T_e$, and that points identified in the Brownian map are leaves.
--
--   Differences from the source:
--   - encoding: a normalized Brownian excursion e and labels Z with the conditional law of §2.4 → e = OAI.FKCRT.standardExcursion B (norm of a 3-dimensional Brownian bridge) for three independent Brownian motions B, and Z with IsBrownianLabels (conditional characteristic functions), on any probability space; reason: the Bessel bridge has the law of the normalized excursion and the characteristic-function identity is the conditional Gaussian law; quantifying over all realizations pins the law
--   - reading: right-increase time defined "similarly" to left-increase time → t ∈ [0,1) and ∃ ε ∈ (0, 1 − t) with f s ≥ f t on [t, t + ε]; reason: the mirror image of the paper's definition under s ↦ 1 − s
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, Lemma 2.1, p.14

import Mathlib
import Definitions.Def_FKCRT
import Definitions.Def_LeGallBrownianMap_IsBrownianLabels
import Definitions.Def_LeGallBrownianMap_IsLeftIncreaseTime
import Definitions.Def_LeGallBrownianMap_IsRightIncreaseTime

open MeasureTheory ProbabilityTheory OAI.FKCRT
open scoped NNReal

namespace LeGallBrownianMap

/-- Le Gall, *Uniqueness and universality of the Brownian map*, arXiv:1105.4842v2, Lemma 2.1,
p.14 (quoted from [18], Lemma 3.2): "With probability one, any point t ∈ [0, 1] which is a
right-increase or a left-increase time of e is neither a right-increase nor a left-increase time
of Z."

For the normalized excursion `e` (realized as `standardExcursion B`) and Brownian labels `Z`,
almost surely, simultaneously for all `t ∈ [0,1]`: if `t` is a right- or left-increase time of `e`
then `t` is neither a right- nor a left-increase time of `Z`.

**Formalization Note.** `(e, Z)` is realized on an arbitrary probability space exactly as in
`LeGallBrownianMap.theorem_1_1`; the statement holds for every such realization. "With
probability one, any point" is one null set for all `t` (`∀ᵐ ω, ∀ t`). -/
theorem lemma_2_1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Fin 3 → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (Z : unitInterval → Ω → ℝ) (hZ : IsBrownianLabels (fun ω => standardExcursion B ω) Z P) :
    ∀ᵐ ω ∂P, ∀ t : unitInterval,
      (IsRightIncreaseTime (standardExcursion B ω) t ∨
          IsLeftIncreaseTime (standardExcursion B ω) t) →
        ¬ IsRightIncreaseTime (fun s => Z s ω) t ∧ ¬ IsLeftIncreaseTime (fun s => Z s ω) t := by sorry

end LeGallBrownianMap
