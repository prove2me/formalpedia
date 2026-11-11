-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_maximal_cartier_extraction_of_iso_s01
-- name    : OAI.MaximalSeshadri.Geometry.maximal_cartier_extraction_of_iso_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:07:28.776973+00:00
-- url     : https://prove2.me/theorems/500b2511-bd77-4f80-853f-24b400c8b1be
-- title:
--   OAI.MaximalSeshadri.Geometry.maximal_cartier_extraction_of_iso_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.maximal_cartier_extraction_of_iso` of [lean/OAI/AlgebraicGeometry/Seshadri/Divisors/MaximalCartierIso.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Divisors/MaximalCartierIso.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`, `open MaximalSeshadri.Frames MaximalSeshadri.Projective`):
--
--   ```lean
--   theorem maximal_cartier_extraction_of_iso_s01 (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
--       (L M : LineBundle X) (d : ℕ) (hd : 0 < d) (E : M.sheaf ≅ (L.pow d).sheaf)
--       {σ : Type} [Fintype σ] (k : ℂ →+* Γ(X,⊤))
--       (s : σ → (O X ⟶ M.sheaf)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (v : σ → ℂ)
--       (hne : sectionCombination k s v ≠ 0)
--       [IsIntegral (sectionIdeal k s hs v).subscheme]
--       (U : X.affineOpens) [Nonempty U.1]
--       [Nonempty ((sectionIdeal k s hs v).subschemeι ⁻¹ᵁ U.1).toScheme]
--       (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
--       (eM : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
--       (hnu : ¬ IsUnit (affineCoefficient U eM (sectionCombination k s v)))
--       (a : ℕ) (t : O X ⟶ (L.pow a).sheaf) (ht : t ≠ 0)
--       (eA : (L.pow a).sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
--       ∃ j n : ℕ, a = j*d+n ∧ ∃ q : O X ⟶ (L.pow n).sheaf, q ≠ 0 ∧
--         pullbackSection (sectionIdeal k s hs v).subschemeι q ≠ 0 ∧
--         Associated ((affineCoefficient U eM (sectionCombination k s v))^j *
--           affineCoefficient U (localPowerFrame U.1 e n) q) (affineCoefficient U eA t)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Frames.O` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.SectionOpens.isoOpen` (definitions bundle `Q223SES002` of this split); `OAI.MaximalSeshadri.Geometry.localPowerFrame`, `OAI.MaximalSeshadri.Geometry.pullbackSection` and `OAI.MaximalSeshadri.Geometry.LineBundle.pow` (definitions bundle `Q223SES005` of this split); `OAI.MaximalSeshadri.Projective.sectionCombination` (definitions bundle `Q223SES006` of this split); `OAI.MaximalSeshadri.Geometry.affineCoefficient` (definitions bundle `Q223SES007` of this split); `OAI.MaximalSeshadri.Projective.sectionIdeal` (definitions bundle `Q223SES009` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle` and `OAI.MaximalSeshadri.Geometry.modulePow` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.Geometry.generated_nodal_all_section_quadrilateral_s01` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Divisors/MaximalCartierIso.lean (declaration OAI.MaximalSeshadri.Geometry.maximal_cartier_extraction_of_iso)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES009

section

attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

variable {X : Scheme.{0}} [IsIntegral X]

theorem maximal_cartier_extraction_of_iso_s01 (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (L M : LineBundle X) (d : ℕ) (hd : 0 < d) (E : M.sheaf ≅ (L.pow d).sheaf)
    {σ : Type} [Fintype σ] (k : ℂ →+* Γ(X,⊤))
    (s : σ → (O X ⟶ M.sheaf)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (v : σ → ℂ)
    (hne : sectionCombination k s v ≠ 0)
    [IsIntegral (sectionIdeal k s hs v).subscheme]
    (U : X.affineOpens) [Nonempty U.1]
    [Nonempty ((sectionIdeal k s hs v).subschemeι ⁻¹ᵁ U.1).toScheme]
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (eM : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (hnu : ¬ IsUnit (affineCoefficient U eM (sectionCombination k s v)))
    (a : ℕ) (t : O X ⟶ (L.pow a).sheaf) (ht : t ≠ 0)
    (eA : (L.pow a).sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    ∃ j n : ℕ, a = j*d+n ∧ ∃ q : O X ⟶ (L.pow n).sheaf, q ≠ 0 ∧
      pullbackSection (sectionIdeal k s hs v).subschemeι q ≠ 0 ∧
      Associated ((affineCoefficient U eM (sectionCombination k s v))^j *
        affineCoefficient U (localPowerFrame U.1 e n) q) (affineCoefficient U eA t) := by
  sorry
end
end MaximalSeshadri.Geometry

end

end OAI
end
