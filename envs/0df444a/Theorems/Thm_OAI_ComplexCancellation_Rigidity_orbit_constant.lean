-- Prove2me | Theorems.Thm_OAI_ComplexCancellation_Rigidity_orbit_constant
-- name    : OAI.ComplexCancellation.Rigidity.orbit_constant
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:43:54.430886+00:00
-- url     : https://prove2.me/theorems/9f7f2701-454d-44b3-8c81-748e7ae6a498
-- title:
--   Polynomial solutions of $d^2+a^2u^3=n$ with $\deg n\le 1$ are constant when $-u(0)^3$ is not a square
-- statement:
--   Let $k$ be a field of characteristic zero and let $a,d,u,n\in k[X]$ be nonzero polynomials with $\deg n\le1$ and
--
--   $$d^2+a^2u^3=n .$$
--
--   Write $u(0)$ for the constant coefficient of $u$, and assume that $-u(0)^3$ is not a square in $k$, i.e. $z^2\neq-u(0)^3$ for every $z\in k$. Then $a$, $d$ and $u$ are constant polynomials:
--
--   $$a=a(0),\qquad d=d(0),\qquad u=u(0).$$
--
--   This is a rigidity statement: under the nonsquare condition, the relation $d^2+a^2u^3=n$ with $n$ of degree at most one admits no nonconstant polynomial solutions. Applied to the polynomials $\exp(XD)r=\sum_m D^m(r)X^m/m!$ attached to a locally nilpotent derivation $D$, with coefficients mapped into a field, it yields the corresponding rigidity statement for derivations: under the analogous nonsquare condition, a locally nilpotent derivation whose second iterate kills $d^2+a^2u^3$ must annihilate $a$, $d$ and $u$.
--
--   **Formalization Note** Degrees are `natDegree`, constant polynomials are written `C (a.coeff 0)`, and $u(0)$ is `u.coeff 0`. The nonsquare hypothesis forces $u(0)\neq0$, since $0=0^2$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/Rigidity.lean#L73-L121

import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps
import Definitions.Def_OAI_Algebra_AffineCancellation_Cylinder
import Definitions.Def_OAI_Algebra_AffineCancellation_Dimension
import Definitions.Def_OAI_Algebra_AffineCancellation_FactorDerivation

open OAI OAI.ComplexCancellation
open Polynomial UniqueFactorizationMonoid UniqueFactorizationDomain
variable {k : Type*} [Field k]

theorem OAI.ComplexCancellation.Rigidity.orbit_constant [CharZero k] {a d u n : k[X]}
    (ha : a ≠ 0) (hd : d ≠ 0) (hu : u ≠ 0) (hn : n ≠ 0)
    (hdeg : n.natDegree ≤ 1) (heq : d ^ 2 + a ^ 2 * u ^ 3 = n)
    (hns : ∀ z : k, z ^ 2 ≠ -(u.coeff 0) ^ 3) :
    a = C (a.coeff 0) ∧ d = C (d.coeff 0) ∧ u = C (u.coeff 0) := by sorry
