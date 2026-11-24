-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramLocal_tensor_ext
-- name    : GlobalTheory.CompanionTheory.SW.GramLocal.tensor_ext
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:05:42.493076+00:00
-- url     : https://prove2.me/theorems/10c7d568-a122-458b-b545-dfa1cb6a9396
-- title:
--   Gram Local: tensor ext
-- statement:
--   The Gram Local construction uses the tensor ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramMatrixLocalGlobal.lean#L66-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramMatrixLocalGlobal.lean#L66-L77

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramMatrixLocalGlobal
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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GramLocal
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E]

theorem GlobalTheory.CompanionTheory.SW.GramLocal.tensor_ext [Module.Finite F E] (z w : AF F ⊗[F] E)
    (h1 : bcE E (fstA F) z = bcE E (fstA F) w)
    (h2 : ∀ v, bcE E (evalV F v) (bcE E (sndA F) z) = bcE E (evalV F v) (bcE E (sndA F) w)) :
    z = w := by sorry
