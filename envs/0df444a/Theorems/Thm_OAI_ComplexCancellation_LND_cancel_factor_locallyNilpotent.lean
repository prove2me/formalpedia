-- Prove2me | Theorems.Thm_OAI_ComplexCancellation_LND_cancel_factor_locallyNilpotent
-- name    : OAI.ComplexCancellation.LND.cancel_factor_locallyNilpotent
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:46:08.784104+00:00
-- url     : https://prove2.me/theorems/18c81eb4-04cd-44db-a118-853a73a16520
-- title:
--   Dividing a locally nilpotent derivation by a nonzero factor preserves local nilpotence
-- statement:
--   Let $k$ be a field of characteristic zero, $R$ an integral domain that is a $k$-algebra, and $S$ a commutative $k$-algebra. Let $f:S\to R$ be an injective $k$-algebra homomorphism, $D$ a locally nilpotent $k$-derivation of $R$ (every element of $R$ is killed by some iterate of $D$), $E$ a $k$-derivation of $S$, and $c\in R$ a nonzero element such that
--
--   $$D\bigl(f(r)\bigr)=c\cdot f\bigl(E(r)\bigr)\qquad\text{for all } r\in S .$$
--
--   Then $E$ is locally nilpotent: for every $r\in S$ there is $m\in\mathbb{N}$ with $E^m(r)=0$.
--
--   The factor $c$ is not required to lie in the kernel of $D$. Taking $S=R$ and $f$ the identity, the statement says that if $D=c\,E$ with $c\neq0$, then $E$ is again locally nilpotent; so a locally nilpotent derivation may be divided by any common factor of its values. With a nontrivial embedding $f$ it shows that a derivation of a subring which becomes a multiple of a locally nilpotent derivation after embedding is itself locally nilpotent.
--
--   **Formalization Note** Local nilpotence is `LND.LocallyNilpotent`, i.e. `∀ r, ∃ n, (E : S → S)^[n] r = 0`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/Order.lean#L45-L62

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
open Polynomial
variable {k R : Type*} [Field k] [CharZero k] [CommRing R] [IsDomain R] [Algebra k R]

theorem OAI.ComplexCancellation.LND.cancel_factor_locallyNilpotent {S : Type*} [CommRing S] [Algebra k S]
    (f : S →ₐ[k] R) (hf : Function.Injective f)
    (D : Derivation k R R) (hD : LocallyNilpotent D)
    (E : Derivation k S S) {c : R} (hc : c ≠ 0)
    (h : ∀ r : S, D (f r) = c * f (E r)) : LocallyNilpotent E := by sorry
