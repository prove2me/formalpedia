-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittE_lin_single
-- name    : GlobalTheory.CompanionTheory.SW.WittE.lin_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:19.80882+00:00
-- url     : https://prove2.me/theorems/93c6f38e-a31f-4d69-b9ae-c21df73ba58b
-- title:
--   Witt E: lin single
-- statement:
--   The Witt E construction uses the lin single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/WittExtensionGlobal.lean#L87-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/WittExtensionGlobal.lean#L87-L88

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

theorem GlobalTheory.CompanionTheory.SW.WittE.lin_single {n : ℕ} (X : Fin n → V) (a : Fin n) : lin X (Pi.single a (1 : E)) = X a := by sorry
