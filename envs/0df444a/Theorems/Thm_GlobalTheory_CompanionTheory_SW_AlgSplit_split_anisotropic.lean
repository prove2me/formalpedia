-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_AlgSplit_split_anisotropic
-- name    : GlobalTheory.CompanionTheory.SW.AlgSplit.split_anisotropic
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:00:57.824747+00:00
-- url     : https://prove2.me/theorems/91b0b248-91df-4e7c-a7ad-e5ee29aa3fd6
-- title:
--   Alg Split: split anisotropic
-- statement:
--   The Alg Split construction uses the split anisotropic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SplitAnisotropic.lean#L18-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SplitAnisotropic.lean#L18-L108

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SplitAnisotropic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.AlgSplit

theorem GlobalTheory.CompanionTheory.SW.AlgSplit.split_anisotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E), IsHermND σ J → ∀ (t : F) (x : Fin (M + 1) → E), t ≠ 0 → hE σ J x x = algebraMap F E t → ∃ (g : GL (Fin (M + 1)) E) (J₁ : Matrix (Fin M) (Fin M) E), IsHermND σ J₁ ∧ blockOne (algebraMap F E t) J₁ = cT (σ : E →+* E) (g : Matrix (Fin (M + 1)) (Fin (M + 1)) E) * J * g ∧ ∀ i, (g : Matrix (Fin (M + 1)) (Fin (M + 1)) E) i 0 = x i := by sorry
