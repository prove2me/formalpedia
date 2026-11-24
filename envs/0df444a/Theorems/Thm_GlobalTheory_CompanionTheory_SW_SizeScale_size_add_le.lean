-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_SizeScale_size_add_le
-- name    : GlobalTheory.CompanionTheory.SW.SizeScale.size_add_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:10:16.862953+00:00
-- url     : https://prove2.me/theorems/05c2ef71-94f2-4b0b-b91e-32210f4f55b0
-- title:
--   Size Scale: size add le
-- statement:
--   The Size Scale construction uses the size add le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsSizeMulLe.lean#L30-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsSizeMulLe.lean#L30-L38

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

theorem GlobalTheory.CompanionTheory.SW.SizeScale.size_add_le (b : Module.Basis (Fin d) F E) (x y : Ainf F ⊗[F] E) :
    sizeInf b (x + y) ≤ sizeInf b x + sizeInf b y := by sorry
