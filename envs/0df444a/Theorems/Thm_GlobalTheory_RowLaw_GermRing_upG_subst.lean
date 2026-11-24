-- Prove2me | Theorems.Thm_GlobalTheory_RowLaw_GermRing_upG_subst
-- name    : GlobalTheory.RowLaw.GermRing.upG_subst
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:30:48.89107+00:00
-- url     : https://prove2.me/theorems/a9e39fa8-35d9-4111-91ec-0aabd4cbd513
-- title:
--   Germ Ring: up G subst
-- statement:
--   The Germ Ring construction uses the up G subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IntegralGermEqGaugedFormalGroupLawExpIntegral.lean#L295-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IntegralGermEqGaugedFormalGroupLawExpIntegral.lean#L295-L299

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

theorem GlobalTheory.RowLaw.GermRing.upG_subst (g : Fin 2) {σ : Type} [Finite σ] {a : σ → MvPowerSeries (I g) C}
    (ha : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ C) :
    upG g (subst a f) = subst (fun s => upG g (a s)) f := by sorry
