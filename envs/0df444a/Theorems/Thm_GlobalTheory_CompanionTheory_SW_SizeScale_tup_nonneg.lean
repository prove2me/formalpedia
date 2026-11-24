-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_SizeScale_tup_nonneg
-- name    : GlobalTheory.CompanionTheory.SW.SizeScale.tup_nonneg
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:11:54.045586+00:00
-- url     : https://prove2.me/theorems/a0c924d1-b2aa-45df-be44-e4481ad0f9a9
-- title:
--   Size Scale: tup nonneg
-- statement:
--   The Size Scale construction uses the tup nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsSizeMulLe.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsSizeMulLe.lean#L26-L28

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
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}

theorem GlobalTheory.CompanionTheory.SW.SizeScale.tup_nonneg {M n : ℕ} (b : Module.Basis (Fin d) F E) (X : Fin n → Fin M → Ainf F ⊗[F] E) :
    0 ≤ sizeTup b X := by sorry
