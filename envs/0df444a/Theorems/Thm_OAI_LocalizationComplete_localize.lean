-- Prove2me | Theorems.Thm_OAI_LocalizationComplete_localize
-- name    : OAI.LocalizationComplete.localize
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T14:46:03.544012+00:00
-- url     : https://prove2.me/theorems/bc8ed25d-03b5-471d-8844-1ef93915d346
-- title:
--   OAI.LocalizationComplete.localize: intermediate lemma from OpenAI, The optimal order of convex-body covering density
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoveringOrder.optimal_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The optimal order of convex-body covering density*, OpenAI Math Release, September 23, 2026, result family 92, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LocalizationComplete.localize` of [lean/OAI/Geometry/TranslativeCovering/LocalizationComplete.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/TranslativeCovering/LocalizationComplete.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LocalizationComplete`, with `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Metric MeasureTheory LatticeAveraging LocalizationGood`, `open PatternGeometry PatternRounding LocalizationRounding`, `open scoped ENNReal BigOperators Classical`):
--
--   ```lean
--   theorem localize {n : ℕ} {I : Type u_2} [Fintype I] (Λ : Submodule ℤ (Space n))
--       [DiscreteTopology Λ] (p : I → Space n) {F : Set (Space n)}
--       (hF : IsAddFundamentalDomain Λ F volume) (hF0 : volume F ≠ 0) (hFtop : volume F ≠ ∞)
--       {a r β C D L h b t u : ℝ} (ha : 0 < a) (hD : 0 < D) (hh : 0 < h) (hC : 0 ≤ C)
--       (hL : D+b ≤ L) (hbuf : u+Real.sqrt n*h/2 ≤ β)
--       (hlip : (2*(n:ℝ)/a)*(Real.sqrt n*h/2) ≤ 1) {N : ℕ} (hN : 0 < N)
--       (hbad : uniformWindow F (good Λ p a r β (ENNReal.ofReal C))ᶜ ≤ 1/100)
--       (hcount : ∫⁻ z,field Λ p (countFn (closedBall (0 : Space n) L)) z ∂uniformWindow F ≤ (N:ℝ≥0∞)/40)
--       (U : PoissonConfig.Config (SphericalLaw.Sphere n))
--       (hcover : ∀ y,∃ (i : I) (l : Λ),y-p i-l.val ∈ RandomBody.body b t U) :
--       ∃ (S : Finset (I×Λ)) (q : S → Space n), S.card ≤ N ∧
--         (∀ i,q i ∈ alphabet n h (L+Real.sqrt n*h/2)) ∧
--         volume (closedBall (0 : Space n) D) ≤ 2*volume
--           (roundedGood q a D (r-Real.sqrt n*h/2) u (2*C)) ∧
--         ∀ y ∈ closedBall (0 : Space n) D,∃ i,y-q i ∈
--           RandomBody.body (b+Real.sqrt n*h/2) (t+Real.sqrt n*h/2) U
--   ```
--
--   **Definitions.** The statement is written with `OAI.LatticeAveraging.Space`, `OAI.LatticeAveraging.field`, `OAI.LatticeAveraging.uniformWindow`, `OAI.LocalizationComplete.Space`, `OAI.LocalizationGood.countFn`, `OAI.LocalizationGood.good`, `OAI.LocalizationRounding.Space`, `OAI.LocalizationRounding.alphabet`, `OAI.PatternGeometry.Space`, `OAI.PatternGeometry.roundedGood`, `OAI.PoissonConfig.Config`, `OAI.RandomBody.body`, `OAI.SphericalLaw.Space` and `OAI.SphericalLaw.Sphere` (definitions bundle `OAIQ16Cd000` of this split).
--
--   **Used by.** The proof of `OAI.AllLatticeExclusion.no_cover` of this split imports it.
-- source:
--   OpenAI, The optimal order of convex-body covering density, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 92; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Translative-covering-densities-of-order-n-log-n-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/TranslativeCovering/LocalizationComplete.lean (declaration OAI.LocalizationComplete.localize)

import Mathlib
import Definitions.Def_OAIQ16Cd000

section

attribute [-instance] _root_.OAI.CapCost.intensity_finite _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2

namespace LocalizationComplete
open Set Metric MeasureTheory LatticeAveraging LocalizationGood
open PatternGeometry PatternRounding LocalizationRounding
open scoped ENNReal BigOperators Classical

theorem localize {n : ℕ} {I : Type u_2} [Fintype I] (Λ : Submodule ℤ (Space n))
    [DiscreteTopology Λ] (p : I → Space n) {F : Set (Space n)}
    (hF : IsAddFundamentalDomain Λ F volume) (hF0 : volume F ≠ 0) (hFtop : volume F ≠ ∞)
    {a r β C D L h b t u : ℝ} (ha : 0 < a) (hD : 0 < D) (hh : 0 < h) (hC : 0 ≤ C)
    (hL : D+b ≤ L) (hbuf : u+Real.sqrt n*h/2 ≤ β)
    (hlip : (2*(n:ℝ)/a)*(Real.sqrt n*h/2) ≤ 1) {N : ℕ} (hN : 0 < N)
    (hbad : uniformWindow F (good Λ p a r β (ENNReal.ofReal C))ᶜ ≤ 1/100)
    (hcount : ∫⁻ z,field Λ p (countFn (closedBall (0 : Space n) L)) z ∂uniformWindow F ≤ (N:ℝ≥0∞)/40)
    (U : PoissonConfig.Config (SphericalLaw.Sphere n))
    (hcover : ∀ y,∃ (i : I) (l : Λ),y-p i-l.val ∈ RandomBody.body b t U) :
    ∃ (S : Finset (I×Λ)) (q : S → Space n), S.card ≤ N ∧
      (∀ i,q i ∈ alphabet n h (L+Real.sqrt n*h/2)) ∧
      volume (closedBall (0 : Space n) D) ≤ 2*volume
        (roundedGood q a D (r-Real.sqrt n*h/2) u (2*C)) ∧
      ∀ y ∈ closedBall (0 : Space n) D,∃ i,y-q i ∈
        RandomBody.body (b+Real.sqrt n*h/2) (t+Real.sqrt n*h/2) U := by
  sorry
end LocalizationComplete

end OAI
end
