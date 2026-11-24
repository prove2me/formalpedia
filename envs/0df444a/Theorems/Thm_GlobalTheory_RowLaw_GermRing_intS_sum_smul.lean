-- Prove2me | Theorems.Thm_GlobalTheory_RowLaw_GermRing_intS_sum_smul
-- name    : GlobalTheory.RowLaw.GermRing.intS_sum_smul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:31:31.277846+00:00
-- url     : https://prove2.me/theorems/bbeae4ae-b127-464b-bb0c-61c4c2139996
-- title:
--   Germ Ring: int S sum smul
-- statement:
--   The Germ Ring construction uses the int S sum smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IntegralGermEqGaugedFormalGroupLawExpIntegral.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IntegralGermEqGaugedFormalGroupLawExpIntegral.lean#L36-L39

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntegralGermEqGaugedFormalGroupLawExpIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.FormalInv MvPowerSeries
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.GermRing
variable {C : Type} [Field C]

theorem GlobalTheory.RowLaw.GermRing.intS_sum_smul {V : VF C} {σ ι : Type} [Fintype ι] {w : ι → C} (hw : ∀ i, V.Ge 0 (w i))
    {f : ι → MvPowerSeries σ C} (hf : ∀ i, IntS V (f i)) : IntS V (∑ i, w i • f i) := by sorry
