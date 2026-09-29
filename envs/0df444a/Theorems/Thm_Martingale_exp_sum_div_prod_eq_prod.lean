-- Prove2me | Theorems.Thm_Martingale_exp_sum_div_prod_eq_prod
-- name    : Martingale.exp_sum_div_prod_eq_prod
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T18:57:44.195105+00:00
-- url     : https://prove2.me/theorems/7095fa78-9380-4725-bc9f-c96d2d6a3776
-- title:
--   $J^{(2)}_n$ factorises: $e^{i\theta \sum_k Z_k}/\prod_k(1+i\theta Z_k) = \prod_k \frac{e^{i\theta Z_k}}{1+i\theta Z_k}$
-- statement:
--   Step 1 of the McLeish proof of the martingale central limit theorem is the decomposition $e^{i\theta S_n} = J^{(1)}_n J^{(2)}_n$ with
--
--   $$J^{(1)}_n = \prod_{k<n}\bigl(1 + i\theta Z_k\bigr), \qquad J^{(2)}_n = \frac{e^{i\theta\sum_{k<n} Z_k}}{\prod_{k<n}(1 + i\theta Z_k)} .$$
--
--   This lemma records that the second factor is itself a product over $k$:
--
--   $$J^{(2)}_n \;=\; \prod_{k<n} \frac{e^{i\theta Z_k}}{1 + i\theta Z_k} .$$
--
--   The proof is the exponential-of-a-sum identity together with distributivity of a finite product over division: $e^{i\theta\sum_k Z_k} = \prod_k e^{i\theta Z_k}$, and a quotient of products is the product of quotients.
--
--   **Why the factorised form matters.** It is what makes the asymptotic analysis of $J^{(2)}_n$ a term-by-term computation. Each factor is $e^{i\theta z}/(1+i\theta z)$ with $z = Z_k$ real, and expanding to second order,
--
--   $$\log\frac{e^{i\theta z}}{1+i\theta z} = i\theta z - \log(1 + i\theta z) = -\frac{\theta^2 z^2}{2} + O\bigl(|\theta z|^3\bigr),$$
--
--   so summing over $k$ gives $\log J^{(2)}_n = -\tfrac{\theta^2}{2}\sum_{k<n} Z_k^2 + o(1)$ once the increments are uniformly negligible. Under the limiting-variance hypothesis $\sum_{k<n} Z_k^2 \Rightarrow \sigma^2$ this yields $J^{(2)}_n \Rightarrow e^{-\theta^2\sigma^2/2}$, which is precisely the Gaussian characteristic function that Lévy's continuity theorem then converts into the central limit theorem.
--
--   Note that no nonvanishing side condition is needed: $1 + i\theta z$ has real part exactly $1$ for real $z$ and $\theta$, so it is never zero and every quotient here is well defined.
-- source:
--   B. M. Brown, "Martingale Central Limit Theorems", Annals of Mathematical Statistics 42 (1971) 59-66, Theorem 2; D. L. McLeish, "Dependent Central Limit Theorems and Invariance Principles", Annals of Probability 2 (1974) 620-628, Theorem 2.3; P. Hall and C. C. Heyde, Martingale Limit Theory and Its Application, Academic Press 1980, Theorem 3.2.

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Exponential

open Finset

theorem Martingale.exp_sum_div_prod_eq_prod {Ω : Type*} (Z : ℕ → Ω → ℝ) (θ : ℝ) (n : ℕ) (ω : Ω) :
    Complex.exp (Complex.I * θ * ((∑ k ∈ Finset.range n, Z k ω : ℝ) : ℂ))
        / ∏ k ∈ Finset.range n, (1 + Complex.I * θ * (Z k ω : ℂ))
      = ∏ k ∈ Finset.range n, (Complex.exp (Complex.I * θ * (Z k ω : ℂ))
          / (1 + Complex.I * θ * (Z k ω : ℂ))) := by sorry
