-- Prove2me | Theorems.Thm_HighEntropyLimit_lindblad_antinormal_monomial
-- name    : HighEntropyLimit.lindblad_antinormal_monomial
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T22:08:06.128975+00:00
-- url     : https://prove2.me/theorems/1d5f3de5-4806-414f-a8ee-0d4d47f80db0
-- title:
--   The Lindblad generator with jump operator $a^\dagger$ on anti-normal monomials
-- statement:
--   Let $\mathcal A$ be a $\mathbb C$-algebra containing $a, a^\dagger$ with $aa^\dagger - a^\dagger a = 1$. Let $\gamma\in\mathbb R$ and $n,m\in\mathbb N$. The Heisenberg-picture Lindblad generator with $H = 0$ and a single jump operator $L = a^\dagger$ (so $L^\dagger = a$) acts on anti-normally ordered monomials by
--   $$\mathcal L\big(a^n(a^\dagger)^m\big) = \frac{\gamma}{2}(n+m)\,a^n(a^\dagger)^m.$$
--   Integrating gives $(a^n(a^\dagger)^m)(t) = (\sqrt\lambda)^{n+m}a^n(a^\dagger)^m$ with $\lambda = e^{\gamma t}$.
--
--   **Formalization Note** The value of $\hbar$ is irrelevant here because $H=0$.
-- source:
--   Carcassi, Landini, Aidala, Classical mechanics as the high-entropy limit of quantum mechanics, arXiv:2411.00972v3 (1 Feb 2026), https://arxiv.org/abs/2411.00972, p. 9, Eqs. (26)-(28), with γ_i = {γ}, L_i = {a†}, H = 0

import Mathlib
import Definitions.Def_HighEntropyLimit_lindblad

namespace HighEntropyLimit
theorem lindblad_antinormal_monomial {A : Type*} [Ring A] [Algebra ℂ A] (a adag : A)
    (hccr : a * adag - adag * a = 1) (hbar γ : ℝ) (n m : ℕ) :
    lindbladHeisenberg hbar 0 [(γ, adag, a)] (a ^ n * adag ^ m) =
      ((γ / 2 * (n + m) : ℝ) : ℂ) • (a ^ n * adag ^ m) := by sorry
end HighEntropyLimit
