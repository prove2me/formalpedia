-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_SizeScale_size_rmul_le
-- name    : GlobalTheory.CompanionTheory.SW.SizeScale.size_rmul_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:10:31.390944+00:00
-- url     : https://prove2.me/theorems/3422c7a5-ec09-4bac-9c3f-8360c6b3041c
-- title:
--   Size Scale: size rmul le
-- statement:
--   The Size Scale construction uses the size rmul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsSizeMulLe.lean#L127-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsSizeMulLe.lean#L127-L160

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsSizeMulLe
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.SizeScale

theorem GlobalTheory.CompanionTheory.SW.SizeScale.size_rmul_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (n M : ℕ) (C : Set (Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E))), IsCompact C → ∃ c : ℝ, 0 < c ∧ ∀ g ∈ C, ∀ X : Fin n → Fin M → Ainf F ⊗[F] E, sizeTup b (rmul (Ainf F) X g) ≤ c * sizeTup b X := by sorry
