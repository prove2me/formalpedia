-- Prove2me | Theorems.Thm_GlobalTheory_HeckeOne_exists_normChar_smooth_homogeneous_inf
-- name    : GlobalTheory.HeckeOne.exists_normChar_smooth_homogeneous_inf
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T14:03:33.312797+00:00
-- url     : https://prove2.me/theorems/111bb8f0-8af8-4ac7-bd80-6c9a12e88c82
-- title:
--   Hecke One: exists norm Char smooth homogeneous inf
-- statement:
--   The Hecke One construction uses the exists norm Char smooth homogeneous inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExtensionEmbeddingMixedSymmOfIsComplex.lean#L129-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExtensionEmbeddingMixedSymmOfIsComplex.lean#L129-L151

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HeckeLEntireAndNonzeroAtOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSmoothMulExtensionOfContinuousChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExtensionEmbeddingMixedSymmOfIsComplex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Classical
open scoped ContDiff
open Formalism.L2.Host (HChar)
open GlobalTheory.CMVal (Ideles)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleNorm)
open GlobalTheory GlobalTheory.HeckeOne
variable (K : Type) [Field K] [NumberField K]
variable {K}

theorem GlobalTheory.HeckeOne.exists_normChar_smooth_homogeneous_inf : ∀ (K : Type) [Field K] [NumberField K] (χ : HChar K), χ.IsUnitary → ∃ (t : ℝ) (φ : mixedSpace K → ℂ), (∀ x y, φ (x * y) = φ x * φ y) ∧ (∀ (r : ℝ) x, 0 < r → φ (r • x) = φ x) ∧ ContDiffOn ℝ ∞ φ {x | mixedEmbedding.norm x ≠ 0} ∧ (∀ x, mixedEmbedding.norm x ≠ 0 → ‖φ x‖ = 1) ∧ ∀ k : Kˣ, φ (mixedEmbedding K (k : K)) = ((((χ * GlobalTheory.HeckeOne.normChar K (-t)).inf k : ℂˣ) : ℂ))⁻¹ := by sorry
