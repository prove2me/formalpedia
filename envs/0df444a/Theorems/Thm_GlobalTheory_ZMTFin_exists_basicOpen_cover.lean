-- Prove2me | Theorems.Thm_GlobalTheory_ZMTFin_exists_basicOpen_cover
-- name    : GlobalTheory.ZMTFin.exists_basicOpen_cover
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:05:44.954725+00:00
-- url     : https://prove2.me/theorems/6be31934-0a3c-492d-b9cd-3bd7ae0fab96
-- title:
--   ZMTFin: exists basic Open cover
-- statement:
--   The ZMTFin construction uses the exists basic Open cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteCompOpenImmersionOfQuasiFinite.lean#L116-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteCompOpenImmersionOfQuasiFinite.lean#L116-L125

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFinsetAwayMapSubalgebraBijectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteCoequifiberedSubalgebraStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelSpecMapIsIsoOverBasicOpenStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormalizationBasicOpenCoverStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AwayMapBijectiveOfRangeEqSubalgebraStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteCompOpenImmersionOfQuasiFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite
open GlobalTheory GlobalTheory.ZMTFin

theorem GlobalTheory.ZMTFin.exists_basicOpen_cover (U X : Scheme.{0}) (f : U ⟶ X) (h₁ : IsSeparated f)
    (h₂ : LocallyOfFiniteType f) (h₃ : QuasiCompact f) (h₄ : LocallyQuasiFinite f)
    (V : X.AffineZariskiSite) :
    ∃ G : Finset (f.normalizationDiagram.obj (Opposite.op V.1)),
      (∀ b ∈ G, letI := (f.normalizationDiagramMap.app (Opposite.op V.1)).hom.toAlgebra
        Algebra.FiniteType Γ(X, V.1) (Localization.Away b)) ∧
      ∀ x : U, f x ∈ V.1 → ∃ b ∈ G, f.toNormalization x ∈
        f.normalizationOpenCover.f V '' (PrimeSpectrum.basicOpen b :
          Set (PrimeSpectrum (f.normalizationDiagram.obj (Opposite.op V.1)))) := by sorry
