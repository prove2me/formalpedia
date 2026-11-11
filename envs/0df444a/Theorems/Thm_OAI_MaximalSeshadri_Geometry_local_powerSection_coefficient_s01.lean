-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_local_powerSection_coefficient_s01
-- name    : OAI.MaximalSeshadri.Geometry.local_powerSection_coefficient_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:14:39.882017+00:00
-- url     : https://prove2.me/theorems/727869ab-9ee1-4800-8a2b-6f89a8e30718
-- title:
--   OAI.MaximalSeshadri.Geometry.local_powerSection_coefficient_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.local_powerSection_coefficient` of [lean/OAI/AlgebraicGeometry/Seshadri/Sheaves/TensorFrames.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Sheaves/TensorFrames.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open CategoryTheory`, `open CategoryTheory.Category CategoryTheory.Functor`, `open CategoryTheory AlgebraicGeometry TopologicalSpace`, `open scoped AlgebraicGeometry`, `open MaximalSeshadri.Frames`):
--
--   ```lean
--   lemma local_powerSection_coefficient_s01 (U : X.Opens) {M : X.Modules}
--       (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
--       (s : structureSheaf X ⟶ M) (n : ℕ) :
--       coefficient (localPowerFrame U e n) (restrictSection U.ι (powerSection s n)) =
--         endValue (powerRestrictionUnit U n).hom *
--           coefficient e (restrictSection U.ι s) ^ n
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Geometry.powerSection` (definitions bundle `Q223SES000` of this split); `OAI.MaximalSeshadri.Frames.coefficient` and `OAI.MaximalSeshadri.Frames.endValue` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.Frames.restrictSection` (definitions bundle `Q223SES004` of this split); `OAI.MaximalSeshadri.Geometry.localPowerFrame` and `OAI.MaximalSeshadri.Geometry.powerRestrictionUnit` (definitions bundle `Q223SES005` of this split); `OAI.MaximalSeshadri.Geometry.modulePow` and `OAI.MaximalSeshadri.Geometry.structureSheaf` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proofs of `OAI.MaximalSeshadri.Geometry.LineBundle.divisible_mixed_extension_s01`, `OAI.MaximalSeshadri.Geometry.LineBundle.power_section_embedding_s01`, `OAI.MaximalSeshadri.Geometry.Surface.H0_finite_s01`, `OAI.MaximalSeshadri.Geometry.Surface.H1_finite_s01`, `OAI.MaximalSeshadri.Geometry.Surface.ample_integral_nodal_section_framed_etale_s01`, `OAI.MaximalSeshadri.Geometry.Surface.ample_quartic_smooth_integral_away_s01`, `OAI.MaximalSeshadri.Geometry.Surface.coprime_embedding_option_s01`, `OAI.MaximalSeshadri.Geometry.Surface.exists_finite_projection_s01`, `OAI.MaximalSeshadri.Geometry.Surface.lineBundle_cohomology_zero_above_two_s01`, `OAI.MaximalSeshadri.Geometry.Surface.pointBlowup_exists_s01`, `OAI.MaximalSeshadri.Geometry.Surface.seshadri_eq_of_curve_lower_s01` and `OAI.MaximalSeshadri.Projective.doublePointQuartics_bertini_s01` of this split import it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Sheaves/TensorFrames.lean (declaration OAI.MaximalSeshadri.Geometry.local_powerSection_coefficient)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES004
import Definitions.Def_Q223SES005

section

attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {X : Scheme}

lemma local_powerSection_coefficient_s01 (U : X.Opens) {M : X.Modules}
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (s : structureSheaf X ⟶ M) (n : ℕ) :
    coefficient (localPowerFrame U e n) (restrictSection U.ι (powerSection s n)) =
      endValue (powerRestrictionUnit U n).hom *
        coefficient e (restrictSection U.ι s) ^ n := by
  sorry

end
end MaximalSeshadri.Geometry

end
end
end

end OAI
end
