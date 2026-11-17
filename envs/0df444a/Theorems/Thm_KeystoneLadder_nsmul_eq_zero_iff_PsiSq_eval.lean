-- Prove2me | Theorems.Thm_KeystoneLadder_nsmul_eq_zero_iff_PsiSq_eval
-- name    : KeystoneLadder.nsmul_eq_zero_iff_PsiSq_eval
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:04:57.360128+00:00
-- url     : https://prove2.me/theorems/52f06e72-7bd7-4466-b576-0c9e6bb4cf49
-- title:
--   Torsion is detected by the squared division denominator
-- statement:
--   Let $k$ be a field, let $W/k$ be an elliptic Weierstrass curve, assume $4≠0$, assume $ψ_m≠0$ as a polynomial for every nonzero $m∈ℤ$, and assume $Ψ_3≠0$. Let $P=(x,y)$ be a nonsingular affine point and let $n∈ℕ$. Writing $S_n=ΨSq_n$, one has $$nP=O ⇔ S_n(x)=0.$$ This is the keystone bridge from group-theoretic torsion to the division-polynomial vanishing criterion. Formalization note: the polynomial index on the right is the integer cast of the natural number $n$.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_KeystoneLadder
import Definitions.Def_PsiInvariant
import Theorems.Thm_KeystoneLadder_XOnly_xLadderRep_three
import Theorems.Thm_KeystoneLadder_XOnly_xLadderRep_four

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical
variable {k : Type*} [Field k]
open KeystoneLadder
open KeystoneLadder.XOnly

theorem KeystoneLadder.nsmul_eq_zero_iff_PsiSq_eval (W : WeierstrassCurve k) [W.IsElliptic]
    (h4 : (4 : k) ≠ 0) (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0) (hc3 : W.Ψ₃ ≠ 0)
    {n : ℕ} {x y : k} (h : (W⁄k).Nonsingular x y) :
    n • (Point.some x y h : (W⁄k).Point) = 0 ↔ (W.ΨSq (n : ℤ)).eval x = 0 := by sorry
