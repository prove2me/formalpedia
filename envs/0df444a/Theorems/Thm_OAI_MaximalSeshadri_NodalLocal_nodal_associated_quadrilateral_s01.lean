-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_NodalLocal_nodal_associated_quadrilateral_s01
-- name    : OAI.MaximalSeshadri.NodalLocal.nodal_associated_quadrilateral_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:16:53.266625+00:00
-- url     : https://prove2.me/theorems/4cbffe1c-02ec-44fe-990c-4ae14426cbc1
-- title:
--   OAI.MaximalSeshadri.NodalLocal.nodal_associated_quadrilateral_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.NodalLocal.nodal_associated_quadrilateral` of [lean/OAI/AlgebraicGeometry/Seshadri/Nodal/NodalAssociated.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Nodal/NodalAssociated.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.NodalLocal`, with `open PowerSeries`):
--
--   ```lean
--   theorem nodal_associated_quadrilateral_s01 (u f g : Bivariate ℂ) (j : ℕ)
--       (d H t k n : ℝ) (hd : 0 < d) (hH : 0 < H) (ht : 0 < t) (hk : 0 < k)
--       (hu : IsUnit u) (hx : restrictX ℂ f ≠ 0) (hz : restrictZ ℂ f ≠ 0)
--       (hcolength : (Module.finrank ℂ (Bivariate ℂ ⧸ intersectionIdeal ℂ f) : ℝ) ≤ n*d*H)
--       (hdegree : n+(j:ℝ)*d=k) (hassoc : Associated ((u*nodeEquation ℂ)^j*f) g)
--       (p : Exponent) (hp : LexInitial (bivariateCoeff g) t p) :
--       ((p.1:ℝ),(p.2:ℝ)) ∈ nodeQuadrilateral
--         (k*(d*H*t/(1+t))) (k*(d*H/(1+t))) (k/d)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Exponent` (definitions bundle `Q223SES000` of this split); `OAI.MaximalSeshadri.NodalLocal.Bivariate`, `OAI.MaximalSeshadri.NodalLocal.nodeEquation`, `OAI.MaximalSeshadri.NodalLocal.restrictX` and `OAI.MaximalSeshadri.NodalLocal.restrictZ` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.nodeQuadrilateral` (definitions bundle `Q223SES003` of this split); `OAI.MaximalSeshadri.LexInitial`, `OAI.MaximalSeshadri.NodalLocal.bivariateCoeff` and `OAI.MaximalSeshadri.NodalLocal.intersectionIdeal` (definitions bundle `Q223SES005` of this split).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.Geometry.generated_nodal_all_section_quadrilateral_s01` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Nodal/NodalAssociated.lean (declaration OAI.MaximalSeshadri.NodalLocal.nodal_associated_quadrilateral)

import Mathlib
import Definitions.Def_Q223SES003
import Definitions.Def_Q223SES005

section

attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaximalSeshadri.NodalLocal
noncomputable section
open PowerSeries

theorem nodal_associated_quadrilateral_s01 (u f g : Bivariate ℂ) (j : ℕ)
    (d H t k n : ℝ) (hd : 0 < d) (hH : 0 < H) (ht : 0 < t) (hk : 0 < k)
    (hu : IsUnit u) (hx : restrictX ℂ f ≠ 0) (hz : restrictZ ℂ f ≠ 0)
    (hcolength : (Module.finrank ℂ (Bivariate ℂ ⧸ intersectionIdeal ℂ f) : ℝ) ≤ n*d*H)
    (hdegree : n+(j:ℝ)*d=k) (hassoc : Associated ((u*nodeEquation ℂ)^j*f) g)
    (p : Exponent) (hp : LexInitial (bivariateCoeff g) t p) :
    ((p.1:ℝ),(p.2:ℝ)) ∈ nodeQuadrilateral
      (k*(d*H*t/(1+t))) (k*(d*H/(1+t))) (k/d) := by
  sorry
end
end MaximalSeshadri.NodalLocal

end

end OAI
end
