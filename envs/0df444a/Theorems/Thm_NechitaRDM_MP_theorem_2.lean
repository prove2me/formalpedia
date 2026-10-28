-- Prove2me | Theorems.Thm_NechitaRDM_MP_theorem_2
-- name    : NechitaRDM.MP.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:48:37.308681+00:00
-- url     : https://prove2.me/theorems/25b3c0bf-56e1-43cd-b84e-a80a8c262e58
-- title:
--   Theorem 2, p. 8 — almost surely the empirical eigenvalue distribution of n⁻¹Wₙ, Wₙ Wishart of parameters n and k(n), converges weakly to μ_c
-- statement:
--   Let $c \in (0,\infty)$ and let $(k(n))_n$ be integers with $\lim_{n\to\infty} k(n)/n = c$. For every $n$ let $W_n = X_n X_n^*$ be a Wishart matrix of parameters $n$ and $k(n)$, i.e. $X_n$ is an $n\times k(n)$ matrix with i.i.d. $\mathcal N_{\mathbb C}(0,1)$ entries. Define the renormalized empirical eigenvalue distribution
--   $$L_n = \frac1n \sum_{i=1}^n \delta_{n^{-1}\lambda_i(W_n)} .$$
--   Then, almost surely, $(L_n)_n$ converges weakly to the Marchenko–Pastur distribution $\mu_c$: there is one null event outside of which
--   $$\int f\,dL_n \longrightarrow \int f\,d\mu_c \qquad \text{for every bounded continuous } f:\mathbb R\to\mathbb R .$$
--
--   This is the classical Marchenko–Pastur theorem for complex Wishart matrices, quoted by the paper from Haagerup–Thorbjørnsen; Theorem 5 is derived from it.
--
--   **Formalization Note** All $X_n$ live on one probability space; nothing is assumed about their joint law across different $n$ (the paper does not couple them, and the almost sure statement holds for every coupling). Weak convergence is tested against all bounded continuous functions with a single null set.
-- source:
--   Nechita, Asymptotics of random density matrices, arXiv:quant-ph/0702154v3, p. 8, Theorem 2 (cited from Haagerup–Thorbjørnsen [4])

import Mathlib
import Definitions.Def_NechitaRDM_MP_Basic

namespace NechitaRDM.MP

open MeasureTheory Filter Topology

/-- **Theorem 2** (p. 8; Haagerup–Thorbjørnsen). For Wishart matrices `Wₙ` of parameters `n`
and `k(n)` with `k(n)/n → c ∈ (0, ∞)`, almost surely the empirical measures
`(1/n) Σᵢ δ_{n⁻¹ λᵢ(Wₙ)}` converge weakly to the Marchenko–Pastur law `μ_c`. -/
theorem theorem_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (c : ℝ) (hc : 0 < c) (k : ℕ → ℕ)
    (hlim : Tendsto (fun n : ℕ => (k n : ℝ) / n) atTop (𝓝 c))
    (X : (n : ℕ) → Ω → Matrix (Fin n) (Fin (k n)) ℂ)
    (hX : ∀ n, IsComplexGaussianMatrix P (X n)) :
    ∀ᵐ ω ∂P, ∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n : ℕ => ∫ x, f x ∂(esd ((n : ℝ)⁻¹) (wishart (X n ω)))) atTop
        (𝓝 (∫ x, f x ∂(marchenkoPastur c))) := by sorry

end NechitaRDM.MP
