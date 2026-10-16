-- Prove2me | Theorems.Thm_OAI_ComplexCancellation_LND_cancel_factor_square_zero
-- name    : OAI.ComplexCancellation.LND.cancel_factor_square_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:46:33.734742+00:00
-- url     : https://prove2.me/theorems/52f34a99-b048-4f00-9d24-5aacbfd445f7
-- title:
--   A degree criterion forcing the square of a divided derivation to annihilate an element
-- statement:
--   Let $k$ be a field of characteristic zero, $R$ an integral domain that is a $k$-algebra, and $S$ a commutative $k$-algebra. Let $D$ be a locally nilpotent $k$-derivation of $R$, and for $r\in R$ let $\deg_D(r)$ denote the degree of the polynomial
--   $$\exp(XD)\,r=\sum_{m\ge0}\frac{D^m(r)}{m!}\,X^m\in R[X],$$
--   that is, the largest $m$ with $D^m(r)\neq0$ (and $\deg_D(0)=0$). Let $f:S\to R$ be an injective $k$-algebra homomorphism, $E$ a $k$-derivation of $S$ and $c\in R$ nonzero with $D(f(r))=c\cdot f(E(r))$ for all $r\in S$. Then for every $v\in S$,
--
--   $$\deg_D\bigl(f(v)\bigr)\le2\deg_D(c)\quad\Longrightarrow\quad E\bigl(E(v)\bigr)=0 .$$
--
--   Each application of $E$ lowers the $D$-degree of the image by $\deg_D(c)+1$, so an element of small $D$-degree can survive at most one application of $E$. This bound is used to show that a transported derivation acts with nilpotency index at most two on suitable elements.
--
--   **Formalization Note** $\deg_D$ is `LND.order D hD`, defined as the `natDegree` of the orbit polynomial `LND.orbit D hD r`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/Order.lean#L69-L85

import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps
import Definitions.Def_OAI_Algebra_AffineCancellation_Cylinder
import Definitions.Def_OAI_Algebra_AffineCancellation_Dimension
import Definitions.Def_OAI_Algebra_AffineCancellation_FactorDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Orbit
import Definitions.Def_OAI_Algebra_AffineCancellation_Order

open OAI OAI.ComplexCancellation OAI.ComplexCancellation.LND
variable {k R S : Type*} [Field k] [CharZero k] [CommRing R] [IsDomain R]
  [CommRing S] [Algebra k S] [Algebra k R]

theorem OAI.ComplexCancellation.LND.cancel_factor_square_zero
    (f : S →ₐ[k] R) (hf : Function.Injective f)
    (D : Derivation k R R) (hD : LocallyNilpotent D)
    (E : Derivation k S S) {c : R} (hc : c ≠ 0)
    (h : ∀ r : S, D (f r)=c*f (E r)) (v : S)
    (ho : order D hD (f v) ≤ 2*order D hD c) : E (E v)=0 := by sorry
