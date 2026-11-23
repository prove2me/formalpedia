-- Prove2me | Theorems.Thm_GlobalTheory_Reg_Transfer_ne_zero_map
-- name    : GlobalTheory.Reg.Transfer.ne_zero_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:52:52.58794+00:00
-- url     : https://prove2.me/theorems/2b8e2674-903a-4629-a151-bbab0bd9565e
-- title:
--   Transfer: ne zero map
-- statement:
--   The Transfer construction uses the ne zero map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/RegularAtCentre.lean#L67-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/RegularAtCentre.lean#L67-L68

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

theorem GlobalTheory.Reg.Transfer.ne_zero_map {x : V} (hx : x ≠ 0) : algebraMap V (FractionRing V) x ≠ 0 := by sorry
