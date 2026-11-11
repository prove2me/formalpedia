-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_coprime_embedding_option_s01
-- name    : OAI.MaximalSeshadri.Geometry.Surface.coprime_embedding_option_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:06:46.263186+00:00
-- url     : https://prove2.me/theorems/5cca8546-6c1a-4cb8-8e94-c8f320cc50e0
-- title:
--   OAI.MaximalSeshadri.Geometry.Surface.coprime_embedding_option_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.Surface.coprime_embedding_option` of [lean/OAI/AlgebraicGeometry/Seshadri/Projective/CoprimeEmbedding.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Projective/CoprimeEmbedding.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite`, `open MaximalSeshadri.Frames MaximalSeshadri.TensorPure MaximalSeshadri.Projective`):
--
--   ```lean
--   theorem Surface.coprime_embedding_option_s01 (S : Surface) (L : LineBundle S.scheme)
--       (hL : L.IsAmple) (a : ℕ) (ha : 0 < a) :
--       ∃ b : ℕ, 0 < b ∧ Nat.Coprime a b ∧ ∃ N : ℕ,
--         ∃ s : Option (Fin N) → GlobalSections S.scheme (L.pow b).sheaf,
--         ∃ hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤,
--           IsClosedImmersion (sectionsMorphism
--             (S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) s hs)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.SectionOpens.isoOpen` (definitions bundle `Q223SES002` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle.pow` (definitions bundle `Q223SES005` of this split); `OAI.MaximalSeshadri.Projective.sectionsMorphism` (definitions bundle `Q223SES009` of this split); `OAI.MaximalSeshadri.Geometry.GlobalSections`, `OAI.MaximalSeshadri.Geometry.LineBundle`, `OAI.MaximalSeshadri.Geometry.Surface`, `OAI.MaximalSeshadri.Geometry.structureSheaf` and `OAI.MaximalSeshadri.Geometry.LineBundle.IsAmple` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.Geometry.Surface.coprime_integral_section_s01` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Projective/CoprimeEmbedding.lean (declaration OAI.MaximalSeshadri.Geometry.Surface.coprime_embedding_option)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES009

section

attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.nonemptyAffineCover_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Frames MaximalSeshadri.TensorPure MaximalSeshadri.Projective

variable {X : Scheme.{0}} {K : Type} [CommRing K]

theorem Surface.coprime_embedding_option_s01 (S : Surface) (L : LineBundle S.scheme)
    (hL : L.IsAmple) (a : ℕ) (ha : 0 < a) :
    ∃ b : ℕ, 0 < b ∧ Nat.Coprime a b ∧ ∃ N : ℕ,
      ∃ s : Option (Fin N) → GlobalSections S.scheme (L.pow b).sheaf,
      ∃ hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤,
        IsClosedImmersion (sectionsMorphism
          (S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) s hs) := by
  sorry

end
end MaximalSeshadri.Geometry

end

end OAI
end
