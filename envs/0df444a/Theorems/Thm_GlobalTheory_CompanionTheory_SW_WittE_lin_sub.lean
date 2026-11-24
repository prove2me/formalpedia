-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittE_lin_sub
-- name    : GlobalTheory.CompanionTheory.SW.WittE.lin_sub
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:13:10.258745+00:00
-- url     : https://prove2.me/theorems/0d582275-376d-42a1-8282-9b42a6fe1372
-- title:
--   Witt E: lin sub
-- statement:
--   The Witt E construction uses the lin sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/WittExtensionGlobal.lean#L96-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/WittExtensionGlobal.lean#L96-L97

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_WittExtensionGlobal
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.WittE
variable {E V : Type} [Field E] [AddCommGroup V] [Module E V] {σ : E →+* E}

theorem GlobalTheory.CompanionTheory.SW.WittE.lin_sub {n : ℕ} (X : Fin n → V) (c d : Fin n → E) : lin X (c - d) = lin X c - lin X d := by sorry
