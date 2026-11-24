-- Prove2me | Theorems.Thm_GlobalTheory_normalization_basicOpen_cover
-- name    : GlobalTheory.normalization_basicOpen_cover
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:12:47.295453+00:00
-- url     : https://prove2.me/theorems/0b7b6afe-9d9b-4e80-82b2-34df3b92e3b2
-- title:
--   Global Theory: normalization basic Open cover
-- statement:
--   The Global Theory construction uses the normalization basic Open cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormalizationBasicOpenCover.lean#L8-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormalizationBasicOpenCover.lean#L8-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormalizationBasicOpenCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory

theorem GlobalTheory.normalization_basicOpen_cover (U X : Scheme.{0}) (f : U ⟶ X) [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] [LocallyQuasiFinite f] (V : X.AffineZariskiSite) :
    ∃ G : Finset (f.normalizationDiagram.obj (Opposite.op V.1)),
      (∀ b ∈ G, letI := (f.normalizationDiagramMap.app (Opposite.op V.1)).hom.toAlgebra;
        Algebra.FiniteType Γ(X, V.1) (Localization.Away b)) ∧
      ∀ x : U, f x ∈ V.1 → ∃ b ∈ G, f.toNormalization x ∈ f.normalizationOpenCover.f V ''
        (PrimeSpectrum.basicOpen b :
          Set (PrimeSpectrum (f.normalizationDiagram.obj (Opposite.op V.1)))) := by sorry
