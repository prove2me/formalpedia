-- Prove2me | Theorems.Thm_ModularCurve_isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_ne_zero_of_ne_1728
-- name    : ModularCurve.isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_ne_zero_of_ne_1728
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/8ab40de4-32b4-53ac-a144-c2b0fa3922c7
-- title:
--   Integral closedness at a generic supersingular node of X₀(q)
-- statement:
--   Let $q$ be a prime with $5 \le q$, let $A$ be a valuation subring of $\overline{\mathbb Q}$, let $k$ be a field of characteristic $q$ and $\mathrm{red} : A \to k$ a ring homomorphism. Let $a \in k$ lie in `ssJSet q k`, i.e. every elliptic Weierstrass curve over $k$ with $j$-invariant $a$ has no nonzero point killed by $q$, and assume $a^{q^2} = a$, $a \neq 0$ and $a \neq 1728$. Let $K$ be an intermediate field of $\overline{\mathbb Q}/\mathbb Q$ with $K$ finite over $\mathbb Q$, write $A_0 =$ `coeffSubring A K` $= A \cap K$ for the intersection of $A$ with $K$ inside $\overline{\mathbb Q}$, and let `redRestrict red K` $: A_0 \to k$ be $\mathrm{red}$ precomposed with the inclusion $A_0 \subseteq A$; assume $a$ has a preimage in $A_0$ under this map. Then the subring `modularLocalizedAtPoint (1 * q) A₀ (redRestrict red K) a (a ^ q)` of $\mathrm{LaurentSeries}(\overline{\mathbb Q})$ — consisting of those Laurent series $f$ for which there are polynomials $r, s \in A_0[X_0, X_1]$ with $s$ not vanishing at $(a, a^q)$ after reduction along `redRestrict red K`, and with $f \cdot \mathrm{modularEval}(s) = \mathrm{modularEval}(r)$, where $\mathrm{modularEval}$ sends $X_0, X_1$ to the $j$-series `jqModC` and its level-$1\cdot q$ companion `jqNModC` and coefficients to constant series — is integrally closed in its fraction field.
--
--   The ring in question is the local ring at the point $(a, a^q)$ of the plane model $\Phi_q(j, j_q) = 0$ of $X_0(q)$ with coefficients in $A \cap K$, and the assertion is its normality at a supersingular node whose $j$-invariant avoids $0$ and $1728$; it is the generic-node case of the normality analysis of these models, complementary to the small primes $q < 5$ and to the special values $j = 0, 1728$. It is used by the statements that an element of the relevant function field integral over this ring already belongs to it, and by the analysis of Frobenius node pairs.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_ne_zero_of_ne_1728.lean

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

theorem ModularCurve.isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_ne_zero_of_ne_1728
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a)
    (hq : 5 ≤ q) (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (hx : ∃ x : ↥(coeffSubring A K), redRestrict red K x = a) :
    IsIntegrallyClosed ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) := by sorry
