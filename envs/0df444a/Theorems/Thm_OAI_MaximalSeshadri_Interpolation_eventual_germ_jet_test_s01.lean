-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Interpolation_eventual_germ_jet_test_s01
-- name    : OAI.MaximalSeshadri.Interpolation.eventual_germ_jet_test_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:16:56.740208+00:00
-- url     : https://prove2.me/theorems/c6c0765b-0ad9-4e5c-ac12-dbc268e33f83
-- title:
--   OAI.MaximalSeshadri.Interpolation.eventual_germ_jet_test_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Interpolation.eventual_germ_jet_test` of [lean/OAI/AlgebraicGeometry/Seshadri/Interpolation/GermInterpolation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Interpolation/GermInterpolation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Interpolation`, with `open scoped BigOperators Pointwise`, `open scoped BigOperators ContDiff`, `open Filter Topology`, `open scoped BigOperators Topology`, `open Filter Set`):
--
--   ```lean
--   theorem eventual_germ_jet_test_s01 (d H T : ℝ) (hd : 0 < d) (hH : 0 < H) (hT : 1 < T)
--       (hweight : ∀ t : ℝ, T < t → d ^ 2 * H * t < (1 + t) ^ 2)
--       (V : ℕ → Submodule ℂ (Exponent → ℂ))
--       [∀ k, FiniteDimensional ℂ (V k)]
--       (hconv : ∀ k c, c ∈ V k → ConvergentSeries c)
--       (hbound : ∀ k, 0 < k → ∀ t, T < t → ∀ e ∈ initialExponentSet (V k) t,
--         ((e.1 : ℝ), (e.2 : ℝ)) ∈ nodeQuadrilateral
--           ((k : ℝ) * (d * H * t / (1 + t)))
--           ((k : ℝ) * (d * H / (1 + t))) ((k : ℝ) / d)) :
--       ∃ r₀ : ℕ, 0 < r₀ ∧ ∀ r : ℕ, r₀ ≤ r →
--         ∀ k m : ℕ, 0 < k → 0 < m → (k : ℝ) * Real.sqrt (H / r) < (m : ℝ) →
--         ∃ R : ℝ, 0 < R ∧ (∀ c ∈ V k, DerivativeSummable c R) ∧
--           ∀ ε : ℝ, 0 < ε → ∃ q : Fin r → ℂ × ℂ, Function.Injective q ∧
--             (∀ j, ‖(q j).1‖ < min ε R ∧ ‖(q j).2‖ < min ε R) ∧
--             Function.Injective (fun f : V k => finiteJetColumn r m q (seriesEval f))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Interpolation.Exponent` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.Interpolation.JetIndex`, `OAI.MaximalSeshadri.Interpolation.finiteJetColumn` and `OAI.MaximalSeshadri.Interpolation.nodeQuadrilateral` (definitions bundle `Q223SES002` of this split); `OAI.MaximalSeshadri.Interpolation.ConvergentSeries`, `OAI.MaximalSeshadri.Interpolation.DerivativeSummable`, `OAI.MaximalSeshadri.Interpolation.initialExponentSet` and `OAI.MaximalSeshadri.Interpolation.seriesEval` (definitions bundle `Q223SES005` of this split).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.Geometry.Surface.eventual_etale_affine_section_test_s01` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Interpolation/GermInterpolation.lean (declaration OAI.MaximalSeshadri.Interpolation.eventual_germ_jet_test)

import Mathlib
import Definitions.Def_Q223SES005

section

attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
open scoped BigOperators ContDiff
open Filter Topology
open scoped BigOperators Topology
open Filter Set

theorem eventual_germ_jet_test_s01 (d H T : ℝ) (hd : 0 < d) (hH : 0 < H) (hT : 1 < T)
    (hweight : ∀ t : ℝ, T < t → d ^ 2 * H * t < (1 + t) ^ 2)
    (V : ℕ → Submodule ℂ (Exponent → ℂ))
    [∀ k, FiniteDimensional ℂ (V k)]
    (hconv : ∀ k c, c ∈ V k → ConvergentSeries c)
    (hbound : ∀ k, 0 < k → ∀ t, T < t → ∀ e ∈ initialExponentSet (V k) t,
      ((e.1 : ℝ), (e.2 : ℝ)) ∈ nodeQuadrilateral
        ((k : ℝ) * (d * H * t / (1 + t)))
        ((k : ℝ) * (d * H / (1 + t))) ((k : ℝ) / d)) :
    ∃ r₀ : ℕ, 0 < r₀ ∧ ∀ r : ℕ, r₀ ≤ r →
      ∀ k m : ℕ, 0 < k → 0 < m → (k : ℝ) * Real.sqrt (H / r) < (m : ℝ) →
      ∃ R : ℝ, 0 < R ∧ (∀ c ∈ V k, DerivativeSummable c R) ∧
        ∀ ε : ℝ, 0 < ε → ∃ q : Fin r → ℂ × ℂ, Function.Injective q ∧
          (∀ j, ‖(q j).1‖ < min ε R ∧ ‖(q j).2‖ < min ε R) ∧
          Function.Injective (fun f : V k => finiteJetColumn r m q (seriesEval f)) := by
  sorry

end MaximalSeshadri.Interpolation

end

end OAI
end
