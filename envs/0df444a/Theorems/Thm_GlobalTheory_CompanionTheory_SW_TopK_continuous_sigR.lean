-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_TopK_continuous_sigR
-- name    : GlobalTheory.CompanionTheory.SW.TopK.continuous_sigR
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:11:14.155425+00:00
-- url     : https://prove2.me/theorems/8d15d42a-4807-4646-a6ca-b04b09859a42
-- title:
--   Top K: continuous sig R
-- statement:
--   The Top K construction uses the continuous sig R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TensorLocallyCompactRing.lean#L38-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TensorLocallyCompactRing.lean#L38-L42

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.TopK
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
omit [IsTopologicalRing R]

theorem GlobalTheory.CompanionTheory.SW.TopK.continuous_sigR (σ : E →ₐ[F] E) : Continuous (sigR R σ) := by sorry
