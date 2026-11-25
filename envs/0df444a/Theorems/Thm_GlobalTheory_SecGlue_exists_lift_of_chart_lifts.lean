-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_exists_lift_of_chart_lifts
-- name    : GlobalTheory.SecGlue.exists_lift_of_chart_lifts
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:51:35.345386+00:00
-- url     : https://prove2.me/theorems/1a38ef40-e78a-4664-86c9-a23b7cc4d446
-- title:
--   Sec Glue: exists lift of chart lifts
-- statement:
--   The Sec Glue construction uses the exists lift of chart lifts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGlobalLiftOfChartLocalLiftsSquareZero.lean#L11-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGlobalLiftOfChartLocalLiftsSquareZero.lean#L11-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecHomExtOfLocalizationAwaySpanEqTopStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGlueSpecLocalizationAwayMorphismsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SquareZeroLocalLiftsCorrectedAgreeOnOverlapsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGlobalLiftOfChartLocalLiftsSquareZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SecGlue

theorem GlobalTheory.SecGlue.exists_lift_of_chart_lifts : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (κ : Type) [Finite κ] (f : κ → R), Ideal.span (Set.range f) = ⊤ → ∀ V : κ → X.left.Opens, (∀ k, IsAffineOpen (V k)) →
    (∀ k, GlobalTheory.SecLift.LiftIn π X g₀ (f k) (V k)) → ∃ e : Sp R ⟶ X.left, e ≫ X.hom = 𝟙 _ ∧ spMap π ≫ e = g₀ := by sorry
