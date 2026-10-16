-- Prove2me | Theorems.Thm_OAI_ComplexCancellation_LND_fixed_of_square_cube
-- name    : OAI.ComplexCancellation.LND.fixed_of_square_cube
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:44:17.069536+00:00
-- url     : https://prove2.me/theorems/e5a8c40b-20bb-42fa-9a0e-9661761215e3
-- title:
--   A locally nilpotent derivation whose second iterate kills $d^2+a^2u^3$ fixes $a$, $d$, $u$ when $-f(u)^3$ is not a square
-- statement:
--   Let $k$ be a field of characteristic zero, $R$ a commutative $k$-algebra, and $K$ a field of characteristic zero that is a $k$-algebra. Let $D$ be a locally nilpotent $k$-derivation of $R$ (for every $r\in R$ there is $m\in\mathbb{N}$ with $D^m(r)=0$), and let $f:R\to K$ be an injective $k$-algebra homomorphism. Let $a,d,u\in R$ be nonzero elements such that $N=d^2+a^2u^3$ satisfies
--   $$N\neq0\qquad\text{and}\qquad D\bigl(D(N)\bigr)=0,$$
--   and assume that $-f(u)^3$ is not a square in $K$, i.e. $z^2\neq-f(u)^3$ for every $z\in K$. Then
--
--   $$D(a)=D(d)=D(u)=0 .$$
--
--   Thus a locally nilpotent derivation that acts linearly on $d^2+a^2u^3$ (in the sense that its second iterate kills it) must fix each of $a$, $d$, $u$, provided the nonsquare condition holds after embedding into a field. In the construction it is applied in the ring $\mathbb{C}[a,d,b,c,u]/(ac-bd-1)$, where $a^3b-a^2u^3-d^2=a^3b-(d^2+a^2u^3)$, as a step in showing that certain homogeneous locally nilpotent derivations vanish.
--
--   **Formalization Note** Local nilpotence is `LND.LocallyNilpotent D`, i.e. `∀ r, ∃ n, (D : R → R)^[n] r = 0`. The ring $R$ is not assumed to be a domain; this follows from the injectivity of $f$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/OrbitRigidity.lean#L13-L40

import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps
import Definitions.Def_OAI_Algebra_AffineCancellation_Cylinder
import Definitions.Def_OAI_Algebra_AffineCancellation_Dimension
import Definitions.Def_OAI_Algebra_AffineCancellation_FactorDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Orbit

open OAI OAI.ComplexCancellation OAI.ComplexCancellation.LND
open Polynomial
variable {k R K : Type*} [Field k] [CharZero k] [CommRing R] [Algebra k R]
  [Field K] [CharZero K] [Algebra k K]

theorem OAI.ComplexCancellation.LND.fixed_of_square_cube (D : Derivation k R R) (hD : LocallyNilpotent D)
    (f : R →ₐ[k] K) (hf : Function.Injective f) {a d u : R}
    (ha : a ≠ 0) (hd : d ≠ 0) (hu : u ≠ 0) (hn : d ^ 2 + a ^ 2 * u ^ 3 ≠ 0)
    (hlin : D (D (d ^ 2 + a ^ 2 * u ^ 3)) = 0)
    (hns : ∀ z : K, z ^ 2 ≠ -(f u) ^ 3) : D a = 0 ∧ D d = 0 ∧ D u = 0 := by sorry
