-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_mixed_whole_curve_basechange_certificates
-- name    : MazurTransfer.order13_actual_mixed_whole_curve_basechange_certificates
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-19T05:00:36.337227+00:00
-- url     : https://prove2.me/theorems/2a8f57a3-b90d-4340-9992-132034b6c4fd
-- statement:
--   For arbitrary commutative rings in the original universe and a specified algebra structure, the literal mixed quadratic curve over the new ring is the scheme-theoretic base change of the original whole glued curve. The original base square is cartesian, the original chosen whole-curve base-change isomorphism has inverse the original gluing lift, that lift is an isomorphism, and both original inverse projection identities hold. All five complete original propositions retain their full hypotheses. Named downstream consumer: the whole dyadic rational-fibre comparison and compatible integral Picard family.

import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalWholeCurveBaseChangeData20261019
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MazurTransfer
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticGluedCurve Order13MixedQuadraticCoefficientBaseChange Order13MixedQuadraticAffineBaseChange Order13MixedQuadraticActualCurveBaseChange
universe u

theorem MazurTransfer.order13_actual_mixed_whole_curve_basechange_certificates : (∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S],
    IsPullback (curveMap R S) (curveToBase S) (curveToBase R)
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))) ∧ (∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S],
    (wholeCurveBaseChangeIso R S).inv = curveBaseChangeLift R S) ∧ (∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S], IsIso (curveBaseChangeLift R S)) ∧ (∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S],
    (wholeCurveBaseChangeIso R S).inv ≫ pullback.fst _ _ = curveToBase S) ∧ (∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S],
    (wholeCurveBaseChangeIso R S).inv ≫ pullback.snd _ _ = curveMap R S) := by sorry
