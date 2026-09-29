-- Prove2me | Theorems.Thm_ModularCurve_isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_eq_zero_or_eq_1728
-- name    : ModularCurve.isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_eq_zero_or_eq_1728
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/e086a431-398c-58ad-9d54-01f75edfa7ec
-- title:
--   Normality of the node ring of X₀(q) at j∈{0,1728}
-- statement:
--   Let $q$ be a prime, $A$ a valuation subring of $\overline{\mathbb Q}$, and $k$ a field of characteristic $q$ equipped with a ring homomorphism $\mathrm{red} : A \to k$. Let $a \in k$ satisfy: $a$ lies in `ssJSet q k`, i.e. every elliptic Weierstrass curve $W$ over $k$ with $W.j = a$ has the property that each affine point $P$ of $W$ with $q \cdot P = 0$ equals $0$; $a^{q^2} = a$; and $a = 0$ or $a = 1728$. Assume $5 \le q$. Let $K$ be an intermediate field of $\overline{\mathbb Q}/\mathbb Q$ with $K$ finite-dimensional over $\mathbb Q$, and write $A_0 =$ `coeffSubring A K` for the subring $A \cap K$ of $\overline{\mathbb Q}$, with `redRestrict red K` the restriction of $\mathrm{red}$ to $A_0$ along this inclusion. Assume $a$ is in the image of `redRestrict red K`, i.e. some $x \in A_0$ reduces to $a$. The conclusion is that the subring $R_0 =$ `modularLocalizedAtPoint (1 * q) A₀ (redRestrict red K) a (a ^ q)` of the Laurent series field over $\overline{\mathbb Q}$ is integrally closed in its field of fractions; here $R_0$ consists of those Laurent series $f$ for which there are two-variable polynomials $r, s$ over $A_0$ with the value of $s$ at $(a, a^q)$ (computed through `redRestrict red K`) nonzero and $f \cdot \mathrm{ev}(s) = \mathrm{ev}(r)$, where $\mathrm{ev}$ substitutes the $q$-expansions `jqModC` and `jqNModC` of level $1 \cdot q$ for the two variables and maps coefficients to constant series.
--
--   This is the normality of the local ring of the plane model $\Phi_q(j, j_q) = 0$ of $X_0(q)$ over the ring of integers $A_0 = A \cap K$ at a supersingular node with $j$-invariant $0$ or $1728$, where the automorphism group of the corresponding elliptic curve is larger and the crossing has width $3$ or $2$; the completed local ring is an $A_{e-1}$ surface singularity in the sense of Deligne–Rapoport, normal but not regular. It is used in the node-descent arguments that test membership in $R_0$ of integral elements of the function field and that analyse Frobenius node pairs.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_eq_zero_or_eq_1728.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_GluedPic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.NodeLocalized

theorem ModularCurve.isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_eq_zero_or_eq_1728
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a)
    (hq : 5 ≤ q) (h01728 : a = 0 ∨ a = 1728)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (hx : ∃ x : ↥(coeffSubring A K), redRestrict red K x = a) :
    IsIntegrallyClosed ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) := by sorry
