-- Prove2me | Theorems.Thm_OAI_ComplexCancellation_LND_primitive_of_order
-- name    : OAI.ComplexCancellation.LND.primitive_of_order
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:47:00.88298+00:00
-- url     : https://prove2.me/theorems/b82f247f-651d-4e36-bd17-8c588187d811
-- title:
--   Removing all common factors $q$ from a locally nilpotent derivation
-- statement:
--   Let $k$ be a field of characteristic zero and $R$ an integral domain that is a $k$-algebra. Let $q\in R$ be nonzero, let $w,b,s\in R$ with $q\nmid s$, let $n\in\mathbb{N}$, and let $D$ be a locally nilpotent $k$-derivation of $R$ (every element is killed by some iterate of $D$) such that
--
--   $$D(q)=0,\qquad D(w)=0,\qquad D(b)=q^n s .$$
--
--   Then there exists a locally nilpotent $k$-derivation $E$ of $R$ with $E(q)=0$ and $E(w)=0$ whose image is not contained in $qR$, i.e. $q\nmid E(r)$ for some $r\in R$.
--
--   The conclusion says that $E$ is primitive with respect to $q$ while still annihilating $q$ and the prescribed invariant $w$. The element $b$ serves as a certificate that the divisibility of the values of $D$ by powers of $q$ is bounded, which is what makes the normalization possible.
--
--   **Formalization Note** Divisibility is `Dvd` in $R$, and local nilpotence is `LND.LocallyNilpotent`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/Primitive.lean#L29-L54

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
variable {k R : Type*} [Field k] [CharZero k] [CommRing R] [IsDomain R] [Algebra k R]

theorem OAI.ComplexCancellation.LND.primitive_of_order (q : R) (hq : q ≠ 0) (w b s : R) (hs : ¬q ∣ s)
    (n : ℕ) (D : Derivation k R R) (hD : LocallyNilpotent D)
    (hDq : D q=0) (hDw : D w=0) (hb : D b=q^n*s) :
    ∃ E : Derivation k R R, LocallyNilpotent E ∧ E q=0 ∧ E w=0 ∧ ∃ r, ¬q ∣ E r := by sorry
