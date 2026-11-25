-- Prove2me | Theorems.Thm_GlobalTheory_T_fromSpecStalk_comp_eq_of_agree_on_closedThickenings
-- name    : GlobalTheory.T.fromSpecStalk_comp_eq_of_agree_on_closedThickenings
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:31:38.532054+00:00
-- url     : https://prove2.me/theorems/7e631fbd-9aa0-4a95-a39a-bb662c274e4a
-- title:
--   T: from Spec Stalk comp eq of agree on closed Thickenings
-- statement:
--   The T construction uses the from Spec Stalk comp eq of agree on closed Thickenings property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FromSpecStalkCompEqOfAgreeOnClosedThickeningsStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FromSpecStalkCompEqOfAgreeOnClosedThickeningsStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FromSpecStalkCompEqOfAgreeOnClosedThickenings
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FromSpecStalkCompEqOfAgreeOnClosedThickeningsStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.fromSpecStalk_comp_eq_of_agree_on_closedThickenings : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (G : Over (Spec (CommRingCat.of R))), LocallyOfFiniteType G.hom → ∀ (b b' : G ⟶ G), (∀ e : ℕ, (Over.pullback (thick R (maximalIdeal R) e)).map b = (Over.pullback (thick R (maximalIdeal R) e)).map b') → ∀ x : G.left, G.hom x = closedPoint R → G.left.fromSpecStalk x ≫ b.left = G.left.fromSpecStalk x ≫ b'.left := by sorry
