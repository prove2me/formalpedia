-- Prove2me | Theorems.Thm_MvPolynomial_squarefree_of_isWeightedHomogeneous_of_aeval_eq_one
-- name    : MvPolynomial.squarefree_of_isWeightedHomogeneous_of_aeval_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/1226026a-14bf-5f91-9db8-1c34a54ceb65
-- title:
--   Squarefreeness of the isobaric relation A(Q,R)=1
-- statement:
--   Let $K$ be a field of characteristic $\ell$ with $\ell$ prime and $\ell \ge 5$. Let $P, Q, R$ be formal power series over $K$ in one variable, each with constant coefficient $1$, such that $Q^3 \neq R^2$, and such that the three relations $12\,(X \cdot P') = P^2 - Q$, $3\,(X \cdot Q') = PQ - R$ and $2\,(X \cdot R') = PR - Q^2$ hold, where $'$ denotes the derivative of power series, so that $X \cdot (\,\cdot\,)'$ is the operator $\theta = q\,d/dq$. Let $A$ be a polynomial in two variables over $K$ which is weighted homogeneous of degree $\ell - 1$ for the weights $4$ and $6$ assigned to the two variables, and suppose that substituting $Q$ for the first variable and $R$ for the second gives the power series $1$. Then $A$ is squarefree in the polynomial ring, i.e. every element whose square divides $A$ is a unit.
--
--   This is the abstract form of part of Swinnerton-Dyer's theorem on the polynomial satisfied by the reductions modulo $\ell$ of the Eisenstein series: taking $P, Q, R$ to be the reductions of $E_2, E_4, E_6$ and $A$ the isobaric polynomial of weight $\ell-1$ expressing $E_{\ell-1} \equiv 1$, the conclusion is that $A$ has no repeated irreducible factor. It is used in the proof that $\ell - 1$ divides the weight of a level-one modular form whose $q$-expansion is congruent to a constant modulo $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPolynomial_squarefree_of_isWeightedHomogeneous_of_aeval_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem MvPolynomial.squarefree_of_isWeightedHomogeneous_of_aeval_eq_one
    {K : Type*} [Field K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (h5 : 5 ≤ ℓ)
    {P Q R : PowerSeries K}
    (hP0 : PowerSeries.constantCoeff P = 1) (hQ0 : PowerSeries.constantCoeff Q = 1)
    (hR0 : PowerSeries.constantCoeff R = 1) (hQR : Q ^ 3 ≠ R ^ 2)
    (hP : 12 * (PowerSeries.X * PowerSeries.derivative K P) = P ^ 2 - Q)
    (hQ : 3 * (PowerSeries.X * PowerSeries.derivative K Q) = P * Q - R)
    (hR : 2 * (PowerSeries.X * PowerSeries.derivative K R) = P * R - Q ^ 2)
    {A : MvPolynomial (Fin 2) K}
    (hA : A.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) (ℓ - 1))
    (hA1 : MvPolynomial.aeval (![Q, R] : Fin 2 → PowerSeries K) A = 1) :
    Squarefree A := by sorry
