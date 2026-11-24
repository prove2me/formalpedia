-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_SizeScale_exists_size_mul_le
-- name    : GlobalTheory.CompanionTheory.SW.SizeScale.exists_size_mul_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:10:23.65756+00:00
-- url     : https://prove2.me/theorems/f1c87001-efdb-4448-84df-312050507985
-- title:
--   Size Scale: exists size mul le
-- statement:
--   The Size Scale construction uses the exists size mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsSizeMulLe.lean#L82-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsSizeMulLe.lean#L82-L123

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

theorem GlobalTheory.CompanionTheory.SW.SizeScale.exists_size_mul_le (b : Module.Basis (Fin d) F E) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x y : Ainf F ⊗[F] E, sizeInf b (x * y) ≤ K * sizeInf b x * sizeInf b y := by sorry
