-- Prove2me | Theorems.Thm_GlobalTheory_ThickStalkEq_fromSpecStalk_comp_eq
-- name    : GlobalTheory.ThickStalkEq.fromSpecStalk_comp_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:07:56.208917+00:00
-- url     : https://prove2.me/theorems/eddad9b2-a4d5-475d-9adf-757c2ec5b829
-- title:
--   Thick Stalk Eq: from Spec Stalk comp eq
-- statement:
--   The Thick Stalk Eq construction uses the from Spec Stalk comp eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FromSpecStalkCompEqOfAgreeOnClosedThickenings.lean#L85-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FromSpecStalkCompEqOfAgreeOnClosedThickenings.lean#L85-L117

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FromSpecStalkCompEqOfAgreeOnClosedThickenings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.ThickStalkEq

theorem GlobalTheory.ThickStalkEq.fromSpecStalk_comp_eq : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (G : Over (Spec (CommRingCat.of R))), LocallyOfFiniteType G.hom → ∀ (b b' : G ⟶ G),
    (∀ e : ℕ, (Over.pullback (thick R (maximalIdeal R) e)).map b =
      (Over.pullback (thick R (maximalIdeal R) e)).map b') →
    ∀ x : G.left, G.hom x = closedPoint R →
      G.left.fromSpecStalk x ≫ b.left = G.left.fromSpecStalk x ≫ b'.left := by sorry
