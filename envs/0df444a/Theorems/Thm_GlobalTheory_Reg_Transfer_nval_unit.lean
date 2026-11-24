-- Prove2me | Theorems.Thm_GlobalTheory_Reg_Transfer_nval_unit
-- name    : GlobalTheory.Reg.Transfer.nval_unit
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:18:29.26995+00:00
-- url     : https://prove2.me/theorems/d6d4bd45-6246-4030-a2cc-dc69f084adc0
-- title:
--   Transfer: nval unit
-- statement:
--   The Transfer construction uses the nval unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/RegularAtCentre.lean#L60-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/RegularAtCentre.lean#L60-L65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_RegularAtCentre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.Transfer
open IsLocalRing Formalism.L2.Pj GlobalTheory.Reg
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem GlobalTheory.Reg.Transfer.nval_unit (e : ℕ) (u : V) (hu : u ∉ maximalIdeal V) : nval V e (algebraMap V (FractionRing V) u) = 0 := by sorry
