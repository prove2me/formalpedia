-- Prove2me | Theorems.Thm_IntQuotHNP_lemma_4_5
-- name    : IntQuotHNP.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:53:14.71898+00:00
-- url     : https://prove2.me/theorems/d2229177-f92c-43da-9869-e26c458c797c
-- title:
--   Lemma 4.5 — endpoint bounds $\Psi_X(1),\ X^N\Psi_X(X)\le\mathrm{poly}_{N,A}(\log p)$; positive-power form
-- statement:
--   1. For every $N\ge3$, $A\ge0$ and constant $C>0$ in (7), there are $c,K,p_0$ such that for every $p\ge p_0$ and every integer $1\le X\le p^{\xi_N}(\log p)^A$, the bound $B=c(\log p)^K$ satisfies
--   $$
--   \Psi_X(1)\le B,\qquad X^N\Psi_X(X)\le B .
--   $$
--   2. For all $N$ and $C,X,p>0$, the function $\Psi_X$ is a finite sum of powers of $u^{-1}$ with positive coefficients: $\Psi_X(u)=\sum_\ell c_\ell(u^{-1})^{r_\ell}$ for every $u>0$, with $c_\ell>0$ and natural $r_\ell$.
--
--   The positive-coefficient form lets the bounds at $u=1,X$ control $u^N\Psi_X(u)$ between them.
--
--   Differences from the source:
--   - generalization: the constant C_N of Lemma 4.4, p prime, and the standing X < p → every constant C > 0, every natural p ≥ p₀, no condition X < p; reason: the estimate is analytic and uses none of these; C_N and prime p are instances
--   - encoding: B = poly_{N,A}(log p) → B = c(log p)^K with c, K depending on N, A and C; reason: this is the meaning of the notation, and for C = C_N the dependence is on N, A only
--   - generalization: the positive-coefficient form of Ψ_X for the parameters of the lemma → the positive-coefficient form for every N, every real C > 0, X > 0 and p > 0, with natural exponents r_ℓ; reason: the expansion of the product (7) uses only positivity of C, X, p; the lemma's parameters are an instance
-- source:
--   Kang, Lee, Provable Recovery from Integer Quotients: Improved Bounds for Nonlinear Hidden Number Problems, STOC 2027 submission (manuscript sha256 605f9dd3…), Lemma 4.5, p.23 (PDF p.24)

import Mathlib
import Definitions.Def_IntQuotHNP_XiN
import Definitions.Def_IntQuotHNP_Psi

namespace IntQuotHNP

/-- **Lemma 4.5 (endpoint bounds).**
Kang, Lee, *Provable Recovery from Integer Quotients*, STOC 2027 submission (manuscript sha256
605f9dd3…), Lemma 4.5, p.23 (PDF p.24): "For fixed N ≥ 3, A ≥ 0, sufficiently large p, and
1 ≤ X ≤ p^{ξ_N}(log p)^A, there is B = poly_{N,A}(log p) such that Ψ_X(1) ≤ B, X^NΨ_X(X) ≤ B.
Moreover, Ψ_X(u) is a finite sum of powers of u^{−1} with positive coefficients."

1. For every `N ≥ 3`, `A ≥ 0` and constant `C > 0` in (7) there are `c`, `K`, `p₀` such that for
   every `p ≥ p₀` and every integer `1 ≤ X ≤ p^{ξ_N}(log p)^A`:
   `Ψ_X(1) ≤ c(log p)^K` and `X^N Ψ_X(X) ≤ c(log p)^K`.
2. For all `N` and `C, X, p > 0` there are finitely many `c_ℓ > 0` and exponents `r_ℓ ∈ ℕ` with
   `Ψ_X(u) = ∑_ℓ c_ℓ (u^{−1})^{r_ℓ}` for every `u > 0`.

**Formalization Note.** `poly_{N,A}(log p)` is `c(log p)^K` with `c, K` depending on `N, A` (and
the constant `C`); `log` is natural, `p^{ξ_N}` and `(log p)^A` are `Real.rpow`. -/
theorem lemma_4_5 :
    (∀ N : ℕ, 3 ≤ N → ∀ A : ℝ, 0 ≤ A → ∀ C : ℝ, 0 < C → ∃ (c : ℝ) (K : ℕ) (p₀ : ℕ),
      ∀ p : ℕ, p₀ ≤ p → ∀ X : ℕ, 1 ≤ X →
        (X : ℝ) ≤ (p : ℝ) ^ xiN N * Real.log p ^ A →
        Psi N C X p 1 ≤ c * Real.log p ^ K ∧ (X : ℝ) ^ N * Psi N C X p X ≤ c * Real.log p ^ K) ∧
    (∀ (N : ℕ) (C X p : ℝ), 0 < C → 0 < X → 0 < p →
      ∃ (L : ℕ) (c : Fin L → ℝ) (r : Fin L → ℕ), (∀ l, 0 < c l) ∧
        ∀ u : ℝ, 0 < u → Psi N C X p u = ∑ l, c l * u⁻¹ ^ r l) := by sorry

end IntQuotHNP
