-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_global_lift_of_chartLocal_lifts_squareZero
-- name    : GlobalTheory.T.exists_global_lift_of_chartLocal_lifts_squareZero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:37:35.161171+00:00
-- url     : https://prove2.me/theorems/318ac259-a46c-405f-b75b-5171057195c0
-- title:
--   T: exists global lift of chart Local lifts square Zero
-- statement:
--   The T construction uses the exists global lift of chart Local lifts square Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGlobalLiftOfChartLocalLiftsSquareZeroStatement.lean#L7-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGlobalLiftOfChartLocalLiftsSquareZeroStatement.lean#L7-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGlobalLiftOfChartLocalLiftsSquareZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LiftAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGlobalLiftOfChartLocalLiftsSquareZeroStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_global_lift_of_chartLocal_lifts_squareZero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (κ : Type) [Finite κ] (f : κ → R), Ideal.span (Set.range f) = ⊤ → ∀ V : κ → X.left.Opens, (∀ k, IsAffineOpen (V k)) →
    (∀ k, GlobalTheory.SecLift.LiftIn π X g₀ (f k) (V k)) → ∃ e : Sp R ⟶ X.left, e ≫ X.hom = 𝟙 _ ∧ spMap π ≫ e = g₀ := by sorry
