-- Prove2me | Theorems.Thm_ModularCurve_NodeLocalized_exists_coeffSubring_inertQuadratic_cubeRoot
-- name    : ModularCurve.NodeLocalized.exists_coeffSubring_inertQuadratic_cubeRoot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/d0555036-9b0b-5cf6-be4f-54086502ae38
-- title:
--   Inert quadratic coefficient extension by a primitive cube root of unity
-- statement:
--   Let $q$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$, let $k$ be a field of characteristic $q$ and let $\mathrm{red} : A \to k$ be a ring homomorphism. For an intermediate field $K$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ write $\operatorname{coeffSubring} A\,K$ for the intersection $A \cap K$ inside $\overline{\mathbb{Q}}$, and $\operatorname{redRestrict}\,\mathrm{red}\,K$ for the composite of the inclusion $A \cap K \hookrightarrow A$ with $\mathrm{red}$. Assume $K$ is finite over $\mathbb{Q}$ and that $\varpi \in A \cap K$ is such that, for every $c \in A \cap K$, one has $\operatorname{redRestrict}\,\mathrm{red}\,K\,(c) = 0$ if and only if $c = \varpi d$ for some $d \in A \cap K$; assume further that $\operatorname{redRestrict}\,\mathrm{red}\,K\,(c^2 + c + 1) \neq 0$ for every $c \in A \cap K$. Then there exist an intermediate field $K'$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite over $\mathbb{Q}$, with $A \cap K \le A \cap K'$ as subrings of $\overline{\mathbb{Q}}$, and an element $\zeta \in A \cap K'$ with $\zeta^2 + \zeta + 1 = 0$, such that every $c \in A \cap K'$ can be written as $c_0 + \zeta c_1$ with $c_0, c_1 \in A \cap K$, and such that, for $c \in A \cap K'$, $\operatorname{redRestrict}\,\mathrm{red}\,K'\,(c) = 0$ holds if and only if $c$ is a multiple of $\varpi$ in $A \cap K'$. Only the inclusion $A \cap K \le A \cap K'$ is asserted, not an inclusion of the fields themselves.
--
--   This is the statement that, when $X^2 + X + 1$ has no root in the residue image of $A \cap K$, adjoining a primitive cube root of unity produces an inert quadratic extension of coefficient rings: the new ring is spanned by $1$ and $\zeta$ over the old one and $\varpi$ remains a generator of the kernel of reduction. It is used when enlarging the coefficient field in the construction of crossing presentations of modular curves localized at a node, and in the analysis of node residues for prolongation tuples.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_NodeLocalized_exists_coeffSubring_inertQuadratic_cubeRoot.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open ModularCurve ModularCurve.NodeLocalized

theorem ModularCurve.NodeLocalized.exists_coeffSubring_inertQuadratic_cubeRoot
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (hirr : ∀ c : ↥(coeffSubring A K), redRestrict red K (c ^ 2 + c + 1) ≠ 0) :
    ∃ (K' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K')
      (hle : coeffSubring A K ≤ coeffSubring A K') (ζ : ↥(coeffSubring A K')),
      ζ ^ 2 + ζ + 1 = 0 ∧
      (∀ c : ↥(coeffSubring A K'), ∃ c₀ c₁ : ↥(coeffSubring A K),
        c = Subring.inclusion hle c₀ + ζ * Subring.inclusion hle c₁) ∧
      (∀ c : ↥(coeffSubring A K'), redRestrict red K' c = 0 ↔ ∃ d, c = Subring.inclusion hle ϖ * d) := by sorry
