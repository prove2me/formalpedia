-- Prove2me | Theorems.Thm_GlobalTheory_Reg_Transfer_vV_unit
-- name    : GlobalTheory.Reg.Transfer.vV_unit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:53:23.970006+00:00
-- url     : https://prove2.me/theorems/fdc4a916-e459-49c4-95e0-259e1d4cd620
-- title:
--   Transfer: v V unit
-- statement:
--   The Transfer construction uses the v V unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/RegularAtCentre.lean#L27-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/RegularAtCentre.lean#L27-L32

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

theorem GlobalTheory.Reg.Transfer.vV_unit (u : V) (hu : u ∉ maximalIdeal V) : vV V (algebraMap V (FractionRing V) u) = 0 := by sorry
