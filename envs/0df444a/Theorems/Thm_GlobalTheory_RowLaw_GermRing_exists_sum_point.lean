-- Prove2me | Theorems.Thm_GlobalTheory_RowLaw_GermRing_exists_sum_point
-- name    : GlobalTheory.RowLaw.GermRing.exists_sum_point
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:31:22.973792+00:00
-- url     : https://prove2.me/theorems/6c67a63c-4d08-4309-ba4d-35a869163f37
-- title:
--   Germ Ring: exists sum point
-- statement:
--   The Germ Ring construction uses the exists sum point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IntegralGermEqGaugedFormalGroupLawExpIntegral.lean#L139-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IntegralGermEqGaugedFormalGroupLawExpIntegral.lean#L139-L153

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntegralGermEqGaugedFormalGroupLawExpIntegral
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst

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

theorem GlobalTheory.RowLaw.GermRing.exists_sum_point (hY : RLaw Y V) {τ ι : Type} (s : Finset ι) (a : ι → κ → MvPowerSeries τ C)
    (ha : ∀ c i, constantCoeff (a c i) = 0) (ia : ∀ c i, IntS V (a c i)) :
    ∃ Φ : κ → MvPowerSeries τ C, (∀ i, constantCoeff (Φ i) = 0) ∧ (∀ i, IntS V (Φ i)) ∧
      ∀ i, subst Φ (Y.lg i) = ∑ c ∈ s, subst (a c) (Y.lg i) := by sorry
