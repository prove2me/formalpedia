-- Prove2me | Theorems.Thm_OAI_ComplexCancellation_LND_kernel_factorially_closed
-- name    : OAI.ComplexCancellation.LND.kernel_factorially_closed
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:44:42.635763+00:00
-- url     : https://prove2.me/theorems/646c0ec0-4852-40ca-9509-213cea332f1c
-- title:
--   The kernel of a locally nilpotent derivation of a domain is factorially closed
-- statement:
--   Let $k$ be a field of characteristic zero, $R$ an integral domain that is a $k$-algebra, and $D$ a locally nilpotent $k$-derivation of $R$ (for every $r\in R$ there is $m\in\mathbb{N}$ with $D^m(r)=0$). If $r,s\in R$ are nonzero and $D(rs)=0$, then
--
--   $$D(r)=0\qquad\text{and}\qquad D(s)=0 .$$
--
--   In other words, the kernel $\ker D$ is factorially closed in $R$: every factor of a nonzero element of $\ker D$ again lies in $\ker D$. This is one of the basic structural properties of locally nilpotent derivations; in the construction it is used to deduce that factors of invariant elements are invariant.
--
--   **Formalization Note** Local nilpotence is `LND.LocallyNilpotent D`, meaning that every element is killed by some iterate of `D`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/Kernel.lean#L25-L48

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
variable {k R : Type*} [Field k] [CharZero k] [CommRing R] [Algebra k R]

theorem OAI.ComplexCancellation.LND.kernel_factorially_closed [IsDomain R] (D : Derivation k R R)
    (hD : LocallyNilpotent D) {r s : R} (hr : r ≠ 0) (hs : s ≠ 0)
    (hrs : D (r * s) = 0) : D r = 0 ∧ D s = 0 := by sorry
