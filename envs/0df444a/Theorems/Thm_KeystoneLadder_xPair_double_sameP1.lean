-- Prove2me | Theorems.Thm_KeystoneLadder_xPair_double_sameP1
-- name    : KeystoneLadder.xPair_double_sameP1
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:03:23.467169+00:00
-- url     : https://prove2.me/theorems/951b6ac6-56c2-4214-81b5-e5972dc7e5dc
-- title:
--   Doubling the EDS x-pair gives the pair at twice the index
-- statement:
--   Let $k$ be a field, let $W$ be a Weierstrass curve over $k$, let $m∈ℤ$ and $x∈k$, assume $4≠0$, assume $ψ_n≠0$ for every nonzero $n∈ℤ$, and assume $Ψ_3≠0$. Put $v_m(x)=(Φ_m(x),ΨSq_m(x))$ and let $D_W$ be homogeneous x-only doubling. Then $$D_W(v_m(x))∼v_{2m}(x),$$ where $∼$ denotes equality up to a nonzero scalar. This connects the polynomial doubling identity with the projective ladder state.
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
variable {k : Type*} [Field k]

theorem KeystoneLadder.xPair_double_sameP1 (W : WeierstrassCurve k) (m : ℤ) (x : k)
    (h4 : (4 : k) ≠ 0) (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0) (hc3 : W.Ψ₃ ≠ 0) :
    SameP1Vec (XOnly.doubleVec (E := W⁄k) (xPair W m x)) (xPair W (2 * m) x) := by sorry
