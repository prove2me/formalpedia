-- Prove2me | Theorems.Thm_MazurTransfer_PlaceOrderOfRangeUnit_ord_image_unit
-- name    : MazurTransfer.PlaceOrderOfRangeUnit.ord_image_unit
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T13:40:54.851397+00:00
-- url     : https://prove2.me/theorems/453e5d1b-28b4-46d5-9416-5fabf64d6f89
-- title:
--   Units mapped into a place valuation ring have order zero
-- statement:
--   Let $v$ be a place of a field extension $F/K$, and let $f:A\to F$ be a unital ring homomorphism from a commutative ring whose image equals the valuation subring of $v$. For every unit $a\in A$, $$\operatorname{ord}_v(f(a))=0.$$ This transfers an affine unit certificate to a vanishing-order calculation at the associated place.
-- source:
--   Original complete ord_image_unit statement and proof from MazurTheorem PlaceOrderOfRangeUnit.lean, Apache-2.0, Vas and contributors. Only the top-level theorem name and namespace context change. The full original closed type is kernel-compared. Named downstream consumer: actual Pell orders at all ordinary-chart closed points.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: an actual ring map whose range is a place's valuation ring
sends units to elements of order zero. Named downstream consumer: the Pell
function at ordinary-chart closed points.
-/
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

noncomputable section
universe u v w
open AlgebraicCurve

theorem MazurTransfer.PlaceOrderOfRangeUnit.ord_image_unit (K : Type u) [Field K] (F : Type v) [Field F] [Algebra K F]
    (A : Type w) [CommRing A] (v : Place K F) (f : A →+* F)
    (hrange : f.range = v.toValuationSubring.toSubring) (a : A) (ha : IsUnit a) :
    v.ord (f a) = 0 := by sorry
