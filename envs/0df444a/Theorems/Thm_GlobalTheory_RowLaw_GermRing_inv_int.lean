-- Prove2me | Theorems.Thm_GlobalTheory_RowLaw_GermRing_inv_int
-- name    : GlobalTheory.RowLaw.GermRing.inv_int
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:31:26.19556+00:00
-- url     : https://prove2.me/theorems/c119cc89-1d48-4451-9fcd-9fc173968918
-- title:
--   Germ Ring: inv int
-- statement:
--   The Germ Ring construction uses the inv int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IntegralGermEqGaugedFormalGroupLawExpIntegral.lean#L155-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IntegralGermEqGaugedFormalGroupLawExpIntegral.lean#L155-L173

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntegralGermEqGaugedFormalGroupLawExpIntegral
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_inv_int

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
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] {Y : RawChart C d I κ} {V : VF C}

theorem GlobalTheory.RowLaw.GermRing.inv_int {σ : Type} [Fintype σ] (A : Matrix σ σ C) (hA : ∀ i j, V.Ge 0 (A i j)) (hd : V.v A.det = 0) :
    IsUnit A ∧ ∀ i j, V.Ge 0 (A⁻¹ i j) := by sorry
