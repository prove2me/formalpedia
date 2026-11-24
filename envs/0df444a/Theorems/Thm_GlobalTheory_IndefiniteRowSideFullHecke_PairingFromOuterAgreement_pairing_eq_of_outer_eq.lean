-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_PairingFromOuterAgreement_pairing_eq_of_outer_eq
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.PairingFromOuterAgreement.pairing_eq_of_outer_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:14:35.862836+00:00
-- url     : https://prove2.me/theorems/61f77b7a-060c-4073-ac48-2fb2be0f82aa
-- title:
--   Pairing From Outer Agreement: pairing eq of outer eq
-- statement:
--   The Pairing From Outer Agreement construction uses the pairing eq of outer eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/SpansOverField.lean#L86-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/SpansOverField.lean#L86-L108

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_SpansOverField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.PairingFromOuterAgreement
open NumberField IsLocalRing ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
variable (E : Type) [Field E] [NumberField E] [IsCMField E] {X : Type} [AddCommGroup X] [Module (𝓞 E) X]

theorem GlobalTheory.IndefiniteRowSideFullHecke.PairingFromOuterAgreement.pairing_eq_of_outer_eq [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X]
    (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (hB : IsBalanced E (fun a c => B a c)) {n m : ℕ}
    (x x' : Fin n → X) (u u' : Fin m → X) (h : outer E x x' = outer E u u') :
    pairing (fun a c => B a c) x x' = pairing (fun a c => B a c) u u' := by sorry
