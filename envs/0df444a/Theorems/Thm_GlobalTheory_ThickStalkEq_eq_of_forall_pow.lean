-- Prove2me | Theorems.Thm_GlobalTheory_ThickStalkEq_eq_of_forall_pow
-- name    : GlobalTheory.ThickStalkEq.eq_of_forall_pow
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:07:32.002487+00:00
-- url     : https://prove2.me/theorems/391aa302-daf4-4621-ad9a-53317cb3362e
-- title:
--   Thick Stalk Eq: eq of forall pow
-- statement:
--   The Thick Stalk Eq construction uses the eq of forall pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FromSpecStalkCompEqOfAgreeOnClosedThickenings.lean#L38-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FromSpecStalkCompEqOfAgreeOnClosedThickenings.lean#L38-L79

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

theorem GlobalTheory.ThickStalkEq.eq_of_forall_pow {X : Scheme.{0}} (A : CommRingCat.{0}) [IsLocalRing A]
    [IsNoetherianRing A] (u u' : Spec A ⟶ X)
    (h : ∀ e : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A ^ (e + 1)))) ≫ u =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A ^ (e + 1)))) ≫ u') :
    u = u' := by sorry
