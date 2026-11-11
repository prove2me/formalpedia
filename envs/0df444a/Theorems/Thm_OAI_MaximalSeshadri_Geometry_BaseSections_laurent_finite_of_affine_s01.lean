-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_BaseSections_laurent_finite_of_affine_s01
-- name    : OAI.MaximalSeshadri.Geometry.BaseSections.laurent_finite_of_affine_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:14:21.506871+00:00
-- url     : https://prove2.me/theorems/2ceded09-1689-45b2-9cf1-7da3d42dd2b6
-- title:
--   OAI.MaximalSeshadri.Geometry.BaseSections.laurent_finite_of_affine_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.BaseSections.laurent_finite_of_affine` of [lean/OAI/AlgebraicGeometry/Seshadri/Sheaves/PlaneModules.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Sheaves/PlaneModules.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry.BaseSections`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`, `open MaximalSeshadri.LaurentPlane`):
--
--   ```lean
--   theorem laurent_finite_of_affine_s01 [IsAffine X] {P : Type} [CommRing P]
--       (kX : K →+* Γ(X,⊤)) (kY : K →+* Γ(Y,⊤))
--       (f : Y ⟶ X) [IsOpenImmersion f] (hk : f.appTop.hom.comp kX = kY)
--       (L : LineBundle X) {N : Y.Modules} (d : L.sheaf.restrict f ≅ N)
--       (a b : Γ(X,⊤)) (hopen : f.opensRange = X.basicOpen (a*b))
--       (u v : Γ(Y,⊤)ˣ) (hu : f.appTop a = u) (hv : f.appTop b = v)
--       (p : P →+* Γ(X,⊤)) (hp : p.Finite) (e : P →+* LaurentPlane.Ring K)
--       (he : f.appTop.hom.comp p = (LaurentPlane.eval kY u v).comp e) :
--       letI := laurentModule kY u v N
--       Module.Finite (LaurentPlane.Ring K) (Sections kY N ⊤)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.LaurentPlane.Ring`, `OAI.MaximalSeshadri.LaurentPlane.eval`, `OAI.MaximalSeshadri.Geometry.BaseSections.Sections`, `OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections` and `OAI.MaximalSeshadri.Geometry.BaseSections.laurentModule` (definitions bundle `Q223SES002` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.Projective.finite_plane_cokernel_s01` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Sheaves/PlaneModules.lean (declaration OAI.MaximalSeshadri.Geometry.BaseSections.laurent_finite_of_affine)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES002

section

attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.LaurentPlane

variable {K : Type} [CommRing K] {X Y : Scheme.{0}}

theorem laurent_finite_of_affine_s01 [IsAffine X] {P : Type} [CommRing P]
    (kX : K →+* Γ(X,⊤)) (kY : K →+* Γ(Y,⊤))
    (f : Y ⟶ X) [IsOpenImmersion f] (hk : f.appTop.hom.comp kX = kY)
    (L : LineBundle X) {N : Y.Modules} (d : L.sheaf.restrict f ≅ N)
    (a b : Γ(X,⊤)) (hopen : f.opensRange = X.basicOpen (a*b))
    (u v : Γ(Y,⊤)ˣ) (hu : f.appTop a = u) (hv : f.appTop b = v)
    (p : P →+* Γ(X,⊤)) (hp : p.Finite) (e : P →+* LaurentPlane.Ring K)
    (he : f.appTop.hom.comp p = (LaurentPlane.eval kY u v).comp e) :
    letI := laurentModule kY u v N
    Module.Finite (LaurentPlane.Ring K) (Sections kY N ⊤) := by
  sorry

end
end MaximalSeshadri.Geometry.BaseSections

end

end OAI
end
