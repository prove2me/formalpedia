-- Prove2me | Theorems.Thm_Glauberman_Dickson_h826_group_order_cases
-- name    : Glauberman.Dickson.h826_group_order_cases
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-12T13:32:37.264147+00:00
-- url     : https://prove2.me/theorems/106e7dbd-5997-444b-b44f-7fbdd9805078
-- title:
--   Arithmetic alternatives in the two-torus Dickson counting equation
-- statement:
--   Suppose positive integers q,a,b are greater than 1, q is coprime to a and b, a divides q−1, and gcd(a,b) divides 2. Assume n is lcm(qa,2a,2b), and u,v,w satisfy qa·u=2a·v=2b·w=n and n=1+(q−1)u+(a−1)v+(b−1)w. Then either (q,a,b,n)=(3,2,5,60), or (a,b,n)=(q−1,q+1,(q+1)q(q−1)), or q is odd and (a,b,n)=((q−1)/2,(q+1)/2,(q+1)q(q−1)/gcd(q−1,2)). This lifts the original private arithmetic lemma into a reusable named theorem.
-- source:
--   Original formalization: Qiuzhen-CFSG/CFSG, original source authors, Apache-2.0; commit 96b2a02085dc678f3e0a97b334c31ada599c55fd; https://github.com/Qiuzhen-CFSG/CFSG/blob/96b2a02085dc678f3e0a97b334c31ada599c55fd/Glauberman/DicksonClassification.lean; declaration Glauberman.Dickson.h826_group_order_cases. arexychen contributes extraction, target-environment replay, theorem-DAG packaging and validation, not original authorship of Dickson classification.

import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Transfer
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
set_option autoImplicit false
universe u v
open scoped Pointwise Classical

theorem Glauberman.Dickson.h826_group_order_cases
    (q a b n u v w : ℕ)
    (hq : 1 < q) (ha : 1 < a) (hb : 1 < b)
    (hqa : Nat.Coprime q a) (hqb : Nat.Coprime q b)
    (hadiv : a ∣ q - 1) (hgcd : Nat.gcd a b ∣ 2)
    (hnlcm : n = Nat.lcm (q * a) (Nat.lcm (2 * a) (2 * b)))
    (hqu : (q * a) * u = n)
    (hav : (2 * a) * v = n)
    (hbw : (2 * b) * w = n)
    (hcount :
      n = 1 + (q - 1) * u + (a - 1) * v + (b - 1) * w) :
    (q = 3 ∧ a = 2 ∧ b = 5 ∧ n = 60) ∨
      (a = q - 1 ∧ b = q + 1 ∧
        n = (q + 1) * q * (q - 1)) ∨
      (Nat.Coprime q 2 ∧
        a = (q - 1) / 2 ∧ b = (q + 1) / 2 ∧
        n = ((q + 1) * q * (q - 1)) / Nat.gcd (q - 1) 2) := by sorry
