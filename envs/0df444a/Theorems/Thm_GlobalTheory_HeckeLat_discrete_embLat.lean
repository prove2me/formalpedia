-- Prove2me | Theorems.Thm_GlobalTheory_HeckeLat_discrete_embLat
-- name    : GlobalTheory.HeckeLat.discrete_embLat
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:04:02.084278+00:00
-- url     : https://prove2.me/theorems/717f1137-74f7-4aa5-a2ba-c24b978e72d0
-- title:
--   Hecke Lat: discrete emb Lat
-- statement:
--   The Hecke Lat construction uses the discrete emb Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PeriodicBoundedGaussianSummableCmType.lean#L71-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PeriodicBoundedGaussianSummableCmType.lean#L71-L83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PeriodicBoundedGaussianSummableCmType
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
noncomputable section
open GlobalTheory GlobalTheory.HeckeLat
variable {K : Type} [Field K] [NumberField K] {I : Type} [Fintype I]

theorem GlobalTheory.HeckeLat.discrete_embLat {φ : I → K →+* ℂ} (hφ : GlobalTheory.CMVal.IsCMType φ) : DiscreteTopology (embLat φ) := by sorry
