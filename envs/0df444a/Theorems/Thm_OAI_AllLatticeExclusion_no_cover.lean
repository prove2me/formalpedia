-- Prove2me | Theorems.Thm_OAI_AllLatticeExclusion_no_cover
-- name    : OAI.AllLatticeExclusion.no_cover
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T14:41:58.359289+00:00
-- url     : https://prove2.me/theorems/d879431b-abfe-4b61-bf3f-42f99ea95ae1
-- title:
--   OAI.AllLatticeExclusion.no_cover: intermediate lemma from OpenAI, The optimal order of convex-body covering density
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoveringOrder.optimal_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The optimal order of convex-body covering density*, OpenAI Math Release, September 23, 2026, result family 92, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AllLatticeExclusion.no_cover` of [lean/OAI/Geometry/TranslativeCovering/AllLatticeExclusion.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/TranslativeCovering/AllLatticeExclusion.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AllLatticeExclusion`, with `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal Topology`, `open Set Filter MeasureTheory`, `open scoped ENNReal Topology`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal Topology`, `open Set Filter MeasureTheory`, `open scoped ENNReal Topology`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open scoped BigOperators Classical`, `open MeasureTheory ProbabilityTheory Set`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open Set MeasureTheory`, `open scoped ENNReal Classical`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal Topology`, `open Set Filter MeasureTheory`, `open scoped ENNReal Topology`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal Topology`, `open Set Filter MeasureTheory`, `open scoped ENNReal Topology`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open scoped BigOperators Classical`, `open MeasureTheory ProbabilityTheory Set`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open Set MeasureTheory`, `open scoped ENNReal Classical`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Metric MeasureTheory SourceParameters LocalizationRates PatternEnumeration SourceLocalization`, `open scoped ENNReal Classical`):
--
--   ```lean
--   theorem no_cover {n : ℕ} [NeZero n] {R : ℝ} (hR : 1≤R) (hRn : R≤(n:ℝ)^2)
--       (hn : 1≤n) (hr : 0 < rminus n) (hβ : 0<β n) (houter : (β n/a)^n≤3)
--       (hinner : (n:ℝ)^2/(2*v)*(rminus n/a)^n≤1/200)
--       (hlip : (2*(n:ℝ)/a)*(Real.sqrt n*h n/2)≤1)
--       (U : PoissonConfig.Config (SphericalLaw.Sphere n))
--       (hvol : 2*v*volume.real (closedBall (0:Space n) a)<volume.real (RandomBody.body (b n) 1 U))
--       (hbad : U ∉ BodySelection.bad R)
--       {I : Type u_2} [Fintype I] (Λ : Submodule ℤ (Space n)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
--       (p : I → Space n) {F : Set (Space n)}
--       (hF : IsAddFundamentalDomain Λ F volume) (hF0 : volume F≠0) (hFtop : volume F≠∞)
--       (hdensity : volume (RandomBody.body (b n) 1 U)*((Fintype.card I:ℝ≥0∞)/volume F)≤ENNReal.ofReal R) :
--       ¬ (∀ y,∃ (i:I) (l:Λ), y-p i-l.val ∈ RandomBody.body (b n) 1 U)
--   ```
--
--   **Definitions.** The statement is written with `OAI.AllLatticeExclusion.Space`, `OAI.BodySelection.bad`, `OAI.LocalizationRates.β`, `OAI.PoissonConfig.Config`, `OAI.RandomBody.body`, `OAI.SourceParameters.a`, `OAI.SourceParameters.b`, `OAI.SourceParameters.h`, `OAI.SourceParameters.rminus`, `OAI.SourceParameters.v`, `OAI.SphericalLaw.Space` and `OAI.SphericalLaw.Sphere` (definitions bundle `OAIQ16Cd000` of this split).
--
--   **Used by.** The proof of `OAI.TranslativeCovering.main` of this split imports it.
-- source:
--   OpenAI, The optimal order of convex-body covering density, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 92; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Translative-covering-densities-of-order-n-log-n-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/TranslativeCovering/AllLatticeExclusion.lean (declaration OAI.AllLatticeExclusion.no_cover)

import Mathlib
import Definitions.Def_OAIQ16Cd000

section

attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
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
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2

namespace AllLatticeExclusion
open Set Metric MeasureTheory SourceParameters LocalizationRates PatternEnumeration SourceLocalization
open scoped ENNReal Classical

theorem no_cover {n : ℕ} [NeZero n] {R : ℝ} (hR : 1≤R) (hRn : R≤(n:ℝ)^2)
    (hn : 1≤n) (hr : 0 < rminus n) (hβ : 0<β n) (houter : (β n/a)^n≤3)
    (hinner : (n:ℝ)^2/(2*v)*(rminus n/a)^n≤1/200)
    (hlip : (2*(n:ℝ)/a)*(Real.sqrt n*h n/2)≤1)
    (U : PoissonConfig.Config (SphericalLaw.Sphere n))
    (hvol : 2*v*volume.real (closedBall (0:Space n) a)<volume.real (RandomBody.body (b n) 1 U))
    (hbad : U ∉ BodySelection.bad R)
    {I : Type u_2} [Fintype I] (Λ : Submodule ℤ (Space n)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (p : I → Space n) {F : Set (Space n)}
    (hF : IsAddFundamentalDomain Λ F volume) (hF0 : volume F≠0) (hFtop : volume F≠∞)
    (hdensity : volume (RandomBody.body (b n) 1 U)*((Fintype.card I:ℝ≥0∞)/volume F)≤ENNReal.ofReal R) :
    ¬ (∀ y,∃ (i:I) (l:Λ), y-p i-l.val ∈ RandomBody.body (b n) 1 U) := by
  sorry
end AllLatticeExclusion

end OAI
end
