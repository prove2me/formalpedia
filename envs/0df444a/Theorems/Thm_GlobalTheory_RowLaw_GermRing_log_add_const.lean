-- Prove2me | Theorems.Thm_GlobalTheory_RowLaw_GermRing_log_add_const
-- name    : GlobalTheory.RowLaw.GermRing.log_add_const
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:55:38.762823+00:00
-- url     : https://prove2.me/theorems/7ace020f-60c8-4a35-b5ed-b5f889bbefb7
-- title:
--   Germ Ring: log add const
-- statement:
--   The Germ Ring construction uses the log add const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IntegralGermEqGaugedFormalGroupLawExpIntegral.lean#L110-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IntegralGermEqGaugedFormalGroupLawExpIntegral.lean#L110-L112

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

theorem GlobalTheory.RowLaw.GermRing.log_add_const (hY : RLaw Y V) {τ : Type} {a b : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) (x : κ) : constantCoeff (subst a (Y.lg x) + subst b (Y.lg x)) = 0 := by sorry
