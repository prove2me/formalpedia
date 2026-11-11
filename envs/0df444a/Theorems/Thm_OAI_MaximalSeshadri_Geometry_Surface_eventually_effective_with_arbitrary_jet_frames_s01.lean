-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_eventually_effective_with_arbitrary_jet_frames_s01
-- name    : OAI.MaximalSeshadri.Geometry.Surface.eventually_effective_with_arbitrary_jet_frames_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:02:24.640205+00:00
-- url     : https://prove2.me/theorems/6f63814d-9776-4947-abcc-f704cab402a0
-- title:
--   OAI.MaximalSeshadri.Geometry.Surface.eventually_effective_with_arbitrary_jet_frames_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.Surface.eventually_effective_with_arbitrary_jet_frames` of [lean/OAI/AlgebraicGeometry/Seshadri/Jets/EffectiveJetFrames.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Jets/EffectiveJetFrames.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace`, `open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini`):
--
--   ```lean
--   theorem Surface.eventually_effective_with_arbitrary_jet_frames_s01 (S : Surface)
--       (L : LineBundle S.scheme) (hL : L.IsAmple) (M : LineBundle S.scheme)
--       (hm : 0 ≤ mixedEuler S L M) {r : ℕ} (m : Fin r → ℕ)
--       (hq : (∑ i, (m i)^2 : ℕ) < selfIntersection S M)
--       (U : Fin r → S.scheme.affineOpens)
--       (t : ∀ i, Fin 2 → Γ(S.scheme,(U i).1))
--       (het : ∀ i, (MvPolynomial.eval₂Hom (openScalars S.structureMap (U i).1) (t i)).Etale)
--       (ρ : ∀ i, letI := (openScalars S.structureMap (U i).1).toAlgebra;
--         Γ(S.scheme,(U i).1) →ₐ[ℂ] ℂ) :
--       ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
--         ∀ e : ∀ i, (M.pow n).sheaf.restrict (U i).1.ι ≅ O (U i).1.toScheme,
--         ∃ s : O S.scheme ⟶ (M.pow n).sheaf, s ≠ 0 ∧
--           ∀ i, affineCoefficient (U i) (e i) s ∈
--             (RingHom.ker (ρ i))^(n*m i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Frames.O` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.ProjectiveBertini.openScalars` (definitions bundle `Q223SES002` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle.pow` (definitions bundle `Q223SES005` of this split); `OAI.MaximalSeshadri.Geometry.affineCoefficient` and `OAI.MaximalSeshadri.Geometry.mixedEuler` (definitions bundle `Q223SES007` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle`, `OAI.MaximalSeshadri.Geometry.Surface`, `OAI.MaximalSeshadri.Geometry.selfIntersection` and `OAI.MaximalSeshadri.Geometry.LineBundle.IsAmple` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.Geometry.curve_lower_of_homogeneous_section_test_s01` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Jets/EffectiveJetFrames.lean (declaration OAI.MaximalSeshadri.Geometry.Surface.eventually_effective_with_arbitrary_jet_frames)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES007

section

attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

theorem Surface.eventually_effective_with_arbitrary_jet_frames_s01 (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) (M : LineBundle S.scheme)
    (hm : 0 ≤ mixedEuler S L M) {r : ℕ} (m : Fin r → ℕ)
    (hq : (∑ i, (m i)^2 : ℕ) < selfIntersection S M)
    (U : Fin r → S.scheme.affineOpens)
    (t : ∀ i, Fin 2 → Γ(S.scheme,(U i).1))
    (het : ∀ i, (MvPolynomial.eval₂Hom (openScalars S.structureMap (U i).1) (t i)).Etale)
    (ρ : ∀ i, letI := (openScalars S.structureMap (U i).1).toAlgebra;
      Γ(S.scheme,(U i).1) →ₐ[ℂ] ℂ) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ∀ e : ∀ i, (M.pow n).sheaf.restrict (U i).1.ι ≅ O (U i).1.toScheme,
      ∃ s : O S.scheme ⟶ (M.pow n).sheaf, s ≠ 0 ∧
        ∀ i, affineCoefficient (U i) (e i) s ∈
          (RingHom.ker (ρ i))^(n*m i) := by
  sorry

end
end MaximalSeshadri.Geometry

end

end OAI
end
