-- Prove2me | Theorems.Thm_KeystoneLadder_xLadderPair_same_xPair_EDS
-- name    : KeystoneLadder.xLadderPair_same_xPair_EDS
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:06:00.435487+00:00
-- url     : https://prove2.me/theorems/c932e1c6-af2e-4e19-af92-45b0f06472db
-- title:
--   The x-only ladder returns the division-polynomial pairs for $n$ and $n+1$
-- statement:
--   Let $W/k$ be an elliptic Weierstrass curve, let $n∈ℕ$ and $x∈k$, assume $4≠0$, all nonzero-index division polynomials $ψ_m$ are nonzero, and $Ψ_3≠0$. Then both $xPair_n$ and $xPair_{n+1}$ are nonzero, and the two outputs of the x-only ladder are projectively equal to them: $$Ladder(x,n)_1∼xPair_n\quad\text{and}\quad Ladder(x,n)_2∼xPair_{n+1}.$$ This validates the ladder representation used in the explicit torsion computations.
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
import Definitions.Def_KeystoneCoprimality
import Definitions.Def_WardSomos
import Definitions.Def_KeystoneDoubling

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical
variable {k : Type*} [Field k]
open KeystoneLadder
open KeystoneLadder.XOnly

theorem KeystoneLadder.xLadderPair_same_xPair_EDS
    (W : WeierstrassCurve k) [W.IsElliptic] (n : ℕ) (x : k)
    (h4 : (4 : k) ≠ 0)
    (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0)
    (hc3 : W.Ψ₃ ≠ 0) :
    xPair W (n : ℤ) x ≠ 0 ∧
    xPair W ((n + 1 : ℕ) : ℤ) x ≠ 0 ∧
    SameP1Vec
      (XOnly.xLadderPair (E := W⁄k) x n).1
      (xPair W (n : ℤ) x) ∧
    SameP1Vec
      (XOnly.xLadderPair (E := W⁄k) x n).2
      (xPair W ((n + 1 : ℕ) : ℤ) x) := by sorry
