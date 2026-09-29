-- Prove2me | Theorems.Thm_IsIntegrallyClosed_exists_isPrime_height_eq_one_mem_ne_of_mul_eq_pow_mul
-- name    : IsIntegrallyClosed.exists_isPrime_height_eq_one_mem_ne_of_mul_eq_pow_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/dfa01aa2-094a-54d3-b475-27ea12116fc4
-- title:
--   A second height-one prime over varpi from a factorisation GH=varpi^e u
-- statement:
--   Let $D$ be a noetherian integrally closed domain (commutative, with no zero divisors), let $\varpi \in D$ be nonzero, and let $Q_1 \subseteq D$ be a prime ideal. Suppose given elements $G, H, u \in D$ and an exponent $e \in \mathbb{N}$ such that $H$ is not a unit of $D$, $H \notin Q_1$, $u$ is a unit of $D$, and $G \cdot H = \varpi^{e} \cdot u$. Then there exists a prime ideal $Q$ of $D$ with $\operatorname{height} Q = 1$, with $\varpi \in Q$, and with $Q \neq Q_1$. Note that $Q_1$ is assumed only to be prime: neither that it has height one nor that it contains $\varpi$ is required, and no local hypothesis on $D$ is imposed beyond noetherianity and integral closedness in its fraction field.
--
--   This is the abstract commutative-algebra form of the assertion that a factorisation $GH = \varpi^e u$ with $H$ a non-unit that is invertible along $Q_1$ forces a height-one prime over $\varpi$ distinct from $Q_1$ — in geometric language, a second branch of the special fibre through the relevant point. It is used in the analysis of prolongation tuples for place specialisations on modular curves, in [`ModularCurve.PlaceSpecialization.ProlongationTuple.hasValue_residueFst_zero_of_residueSnd_eq_zero_of_mem_jIntegralClosure`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.hasValue_residueFst_zero_of_residueSnd_eq_zero_of_mem_jIntegralClosure).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsIntegrallyClosed_exists_isPrime_height_eq_one_mem_ne_of_mul_eq_pow_mul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsIntegrallyClosed.exists_isPrime_height_eq_one_mem_ne_of_mul_eq_pow_mul
    {D : Type*} [CommRing D] [IsDomain D] [IsNoetherianRing D] [IsIntegrallyClosed D]
    (ϖ : D) (hϖ : ϖ ≠ 0)
    (Q₁ : Ideal D) [Q₁.IsPrime]
    (G H u : D) (e : ℕ) (hH : ¬ IsUnit H) (hHQ₁ : H ∉ Q₁)
    (hu : IsUnit u) (hGH : G * H = ϖ ^ e * u) :
    ∃ Q : Ideal D, Q.IsPrime ∧ Q.height = 1 ∧ ϖ ∈ Q ∧ Q ≠ Q₁ := by sorry
