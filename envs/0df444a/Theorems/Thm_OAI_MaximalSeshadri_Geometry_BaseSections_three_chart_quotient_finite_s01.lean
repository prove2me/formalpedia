-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_BaseSections_three_chart_quotient_finite_s01
-- name    : OAI.MaximalSeshadri.Geometry.BaseSections.three_chart_quotient_finite_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:14:18.068939+00:00
-- url     : https://prove2.me/theorems/122bf2f7-014e-4963-994c-81f9af11661f
-- title:
--   OAI.MaximalSeshadri.Geometry.BaseSections.three_chart_quotient_finite_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.BaseSections.three_chart_quotient_finite` of [lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/PlaneCechFinite.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/PlaneCechFinite.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry.BaseSections`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`, `open MaximalSeshadri.LaurentPlane`):
--
--   ```lean
--   theorem three_chart_quotient_finite_s01 [IsAffine A] [IsAffine B] [IsAffine C]
--       (kA : K →+* Γ(A,⊤)) (kB : K →+* Γ(B,⊤))
--       (kC : K →+* Γ(C,⊤)) (kW : K →+* Γ(W,⊤))
--       (a : W ⟶ A) (b : W ⟶ B) (c : W ⟶ C)
--       [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion c]
--       (hka : a.appTop.hom.comp kA = kW) (hkb : b.appTop.hom.comp kB = kW)
--       (hkc : c.appTop.hom.comp kC = kW)
--       (LA : LineBundle A) (LB : LineBundle B) (LC : LineBundle C) (N : W.Modules)
--       (ea : LA.sheaf.restrict a ≅ N) (eb : LB.sheaf.restrict b ≅ N)
--       (ec : LC.sheaf.restrict c ≅ N)
--       (u v : Γ(W,⊤)ˣ)
--       (ax : Γ(A,⊤)ˣ) (ay : Γ(A,⊤)) (bx : Γ(B,⊤)) (by' : Γ(B,⊤)ˣ)
--       (cx : Γ(C,⊤)ˣ) (cy : Γ(C,⊤))
--       (hax : Units.map a.appTop.hom ax = u) (hay : a.appTop ay = v)
--       (hbx : b.appTop bx = u) (hby : Units.map b.appTop.hom by' = v)
--       (hcx : Units.map c.appTop.hom cx = u*v⁻¹) (hcy : c.appTop cy = ↑(v⁻¹))
--       (ha : a.opensRange = A.basicOpen ay) (hb : b.opensRange = B.basicOpen bx)
--       (hc : c.opensRange = C.basicOpen cy)
--       (hfin : letI := laurentModule kW u v N
--         Module.Finite (LaurentPlane.Ring K) (Sections kW N ⊤)) :
--       Module.Finite K (Sections kW N ⊤ ⧸
--         (((chartMap kA kW a hka LA.sheaf ea).range ⊔
--           (chartMap kB kW b hkb LB.sheaf eb).range) ⊔
--           (chartMap kC kW c hkc LC.sheaf ec).range))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.LaurentPlane.Ring`, `OAI.MaximalSeshadri.Geometry.BaseSections.Sections`, `OAI.MaximalSeshadri.Geometry.BaseSections.baseModule`, `OAI.MaximalSeshadri.Geometry.BaseSections.chartMap`, `OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections` and `OAI.MaximalSeshadri.Geometry.BaseSections.laurentModule` (definitions bundle `Q223SES002` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.Projective.finite_plane_cokernel_s01` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/PlaneCechFinite.lean (declaration OAI.MaximalSeshadri.Geometry.BaseSections.three_chart_quotient_finite)

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

variable {K : Type} [Field K] {A B C W : Scheme.{0}}

theorem three_chart_quotient_finite_s01 [IsAffine A] [IsAffine B] [IsAffine C]
    (kA : K →+* Γ(A,⊤)) (kB : K →+* Γ(B,⊤))
    (kC : K →+* Γ(C,⊤)) (kW : K →+* Γ(W,⊤))
    (a : W ⟶ A) (b : W ⟶ B) (c : W ⟶ C)
    [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion c]
    (hka : a.appTop.hom.comp kA = kW) (hkb : b.appTop.hom.comp kB = kW)
    (hkc : c.appTop.hom.comp kC = kW)
    (LA : LineBundle A) (LB : LineBundle B) (LC : LineBundle C) (N : W.Modules)
    (ea : LA.sheaf.restrict a ≅ N) (eb : LB.sheaf.restrict b ≅ N)
    (ec : LC.sheaf.restrict c ≅ N)
    (u v : Γ(W,⊤)ˣ)
    (ax : Γ(A,⊤)ˣ) (ay : Γ(A,⊤)) (bx : Γ(B,⊤)) (by' : Γ(B,⊤)ˣ)
    (cx : Γ(C,⊤)ˣ) (cy : Γ(C,⊤))
    (hax : Units.map a.appTop.hom ax = u) (hay : a.appTop ay = v)
    (hbx : b.appTop bx = u) (hby : Units.map b.appTop.hom by' = v)
    (hcx : Units.map c.appTop.hom cx = u*v⁻¹) (hcy : c.appTop cy = ↑(v⁻¹))
    (ha : a.opensRange = A.basicOpen ay) (hb : b.opensRange = B.basicOpen bx)
    (hc : c.opensRange = C.basicOpen cy)
    (hfin : letI := laurentModule kW u v N
      Module.Finite (LaurentPlane.Ring K) (Sections kW N ⊤)) :
    Module.Finite K (Sections kW N ⊤ ⧸
      (((chartMap kA kW a hka LA.sheaf ea).range ⊔
        (chartMap kB kW b hkb LB.sheaf eb).range) ⊔
        (chartMap kC kW c hkc LC.sheaf ec).range)) := by
  sorry

end
end MaximalSeshadri.Geometry.BaseSections

end

end OAI
end
