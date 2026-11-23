-- Prove2me | Theorems.Thm_GlobalTheory_Reg_Transfer_nval_nonneg
-- name    : GlobalTheory.Reg.Transfer.nval_nonneg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:10:04.77826+00:00
-- url     : https://prove2.me/theorems/49977dbb-7392-4909-b1b6-757b00409990
-- title:
--   Transfer: nval nonneg
-- statement:
--   The Transfer construction uses the nval nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/RegularAtCentre.lean#L51-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/RegularAtCentre.lean#L51-L58

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

theorem GlobalTheory.Reg.Transfer.nval_nonneg (e : ℕ) (w : V) : 0 ≤ nval V e (algebraMap V (FractionRing V) w) := by sorry
