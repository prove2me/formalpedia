-- Prove2me | Theorems.Thm_ModularCurve_isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_pow_sq_ne
-- name    : ModularCurve.isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_pow_sq_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/53080f23-11bc-538b-8175-f83014842402
-- title:
--   Normality of the plane model of X₀(q) at (a,a^q)
-- statement:
--   Let $q$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb Q}$, let $k$ be a field of characteristic $q$ and let $\mathrm{red}\colon A \to k$ be a ring homomorphism. Let $a \in k$ satisfy $a^{q^2} \neq a$. Let $K$ be an intermediate field of $\overline{\mathbb Q}/\mathbb Q$ that is finite-dimensional over $\mathbb Q$, and write $A_0 = \mathtt{coeffSubring}\,A\,K = A \cap K$ for the intersection of $A$ with $K$ inside $\overline{\mathbb Q}$, with $\mathrm{red}_0 = \mathtt{redRestrict}$ the composite of the inclusion $A_0 \hookrightarrow A$ with $\mathrm{red}$. Assume there is $x \in A_0$ with $\mathrm{red}_0(x) = a$. Then the subring $\mathtt{modularLocalizedAtPoint}\,(1 \cdot q)\,A_0\,\mathrm{red}_0\,a\,(a^q)$ of the Laurent series field over $\overline{\mathbb Q}$ — consisting of those Laurent series $f$ for which there are two-variable polynomials $r, s$ over $A_0$ with $s$ not vanishing at $(a, a^q)$ after applying $\mathrm{red}_0$ to its coefficients, and $f \cdot s(j, j_q) = r(j, j_q)$, where $s(j,j_q)$ denotes the image of $s$ under the substitution of the $q$-expansions of $j$ and of $j$ at level $1 \cdot q$ with coefficients mapped to constant series — is integrally closed in its field of fractions.
--
--   This asserts that the localisation of the plane model $A_0[X,Y]/(\Phi_q)$ of $X_0(q)$, realised inside Laurent series via $q$-expansions, is normal at the point $(a, a^q)$ of its special fibre when $a$ does not lie in $\mathbb F_{q^2}$, that is, at the smooth points of the first branch away from its intersection with the second. It is the ring-theoretic input for the Hartogs-type extension statement [`ModularCurve.NodeLocalized.mem_modularLocalizedAtPoint_of_mem_modularLocalized_of_isIntegral`](thm.html#ModularCurve.NodeLocalized.mem_modularLocalizedAtPoint_of_mem_modularLocalized_of_isIntegral), which places an integral function regular in the Gauss sense into this local ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_pow_sq_ne.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.NodeLocalized

theorem ModularCurve.isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_pow_sq_ne
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q] [DecidableEq k]
    (red : A →+* k) (a : k) (ha : a ^ (q ^ 2) ≠ a)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a) :
    IsIntegrallyClosed ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) := by sorry
