-- Prove2me | Theorems.Thm_KeystoneLadder_XOnly_xPair_diffAdd_sameP1_core_order
-- name    : KeystoneLadder.XOnly.xPair_diffAdd_sameP1_core_order
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:06:45.34939+00:00
-- url     : https://prove2.me/theorems/62b64be8-a044-42f6-a5d7-e0fea4844599
-- title:
--   Differential addition of adjacent EDS pairs gives the odd-index pair
-- statement:
--   Let $k$ be a field, let $W/k$ be an elliptic Weierstrass curve, let $m∈ℤ$ and $x∈k$, assume $4≠0$, assume $ψ_n≠0$ for every nonzero $n∈ℤ$, and assume $Ψ_3≠0$. Put $v_n(x)=(Φ_n(x),ΨSq_n(x))$, and let $A_W$ be total differential addition. Then $$A_W(v_m(x),v_{m+1}(x),v_1(x))∼v_{2m+1}(x).$$ This is the projective core of the odd ladder transition.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_KeystoneDoubling
import Definitions.Def_KeystoneLadder
import Definitions.Def_WardSomos

open Polynomial WeierstrassCurve
open scoped Classical
open KeystoneLadder
open KeystoneLadder.XOnly
open Polynomial
variable {k : Type*} [Field k]

theorem KeystoneLadder.XOnly.xPair_diffAdd_sameP1_core_order
    (W : WeierstrassCurve k) [W.IsElliptic] (m : ℤ) (x : k)
    (h4 : (4 : k) ≠ 0) (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0) (hc3 : W.Ψ₃ ≠ 0) :
    SameP1Vec
      (diffAddOrInfVec (E := W⁄k)
        (xPair W m x) (xPair W (m + 1) x) (xPair W 1 x))
      (xPair W (2 * m + 1) x) := by sorry
