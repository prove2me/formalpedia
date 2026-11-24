-- Prove2me | Theorems.Thm_GlobalTheory_Reg_Transfer_vV_nonneg
-- name    : GlobalTheory.Reg.Transfer.vV_nonneg
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:19:12.434845+00:00
-- url     : https://prove2.me/theorems/4cbf4111-de3b-4338-bece-64b0ad28f13e
-- title:
--   Transfer: v V nonneg
-- statement:
--   The Transfer construction uses the v V nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/RegularAtCentre.lean#L15-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/RegularAtCentre.lean#L15-L25

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

theorem GlobalTheory.Reg.Transfer.vV_nonneg (w : V) (hw : w ≠ 0) : 0 ≤ vV V (algebraMap V (FractionRing V) w) := by sorry
