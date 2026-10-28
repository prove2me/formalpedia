-- Prove2me | Theorems.Thm_NechitaRDM_MP_theorem_5
-- name    : NechitaRDM.MP.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:48:50.162988+00:00
-- url     : https://prove2.me/theorems/d1a60955-fe83-4f6e-9bc0-a7d47a3c7372
-- title:
--   Theorem 5, p. 14 — for ρₙ ∼ μ_{n,k(n)} with k(n)/n → c, the empirical distribution of cnλᵢ(ρₙ) converges almost surely to the Marchenko–Pastur law μ_c
-- statement:
--   Let $c \in (0,\infty)$ and let $(k(n))_n$ be integers with $\lim_{n\to\infty} k(n)/n = c$. Let $(\rho_n)_n$ be random density matrices such that, for every $n$, $\rho_n$ has the induced distribution $\mu_{n,k(n)}$ (the partial trace over a $k(n)$-dimensional environment of a uniformly distributed pure state of $\mathbb C^n \otimes \mathbb C^{k(n)}$). Define the renormalized empirical distribution of $\rho_n$ by
--   $$L_n = \frac1n \sum_{i=1}^n \delta_{c\,n\,\lambda_i(\rho_n)},$$
--   where $\lambda_1(\rho_n), \dots, \lambda_n(\rho_n)$ are the eigenvalues of $\rho_n$. Then, almost surely, $(L_n)_n$ converges weakly to the Marchenko–Pastur distribution
--   $$\mu_c = \max\{1-c, 0\}\,\delta_0 + \frac{\sqrt{(x-a)(b-x)}}{2\pi x}\,\mathbf 1_{[a,b]}(x)\,dx, \qquad a = (\sqrt c-1)^2,\ b = (\sqrt c+1)^2 :$$
--   there is one null event outside of which $\int f\,dL_n \to \int f\,d\mu_c$ for every bounded continuous $f$.
--
--   This is the main result on the second model of the paper, in which both the system and its environment grow: the spectrum of a typical reduced state of a large random bipartite pure state, magnified by $cn$, follows the Marchenko–Pastur law.
--
--   **Formalization Note** The hypothesis is the law of $\rho_n$ (`HasInducedLaw`), not the Gaussian formula of Lemma 1. It is assumed for every $n \ge 1$, together with $k(n) \ge 1$, because $\mu_{n,0}$ and $\mu_{0,k}$ are undefined (there are no pure states in dimension $0$). All $\rho_n$ live on one probability space and nothing is assumed about their joint law across $n$: the paper never couples them, and the statement holds for every coupling. The rescaling is $c\,n$ with $c$ the limit of $k(n)/n$, as in eq. (49).
-- source:
--   Nechita, Asymptotics of random density matrices, arXiv:quant-ph/0702154v3, p. 14, Theorem 5 (eq. (49))

import Mathlib
import Definitions.Def_NechitaRDM_MP_Basic

namespace NechitaRDM.MP

open MeasureTheory Filter Topology

/-- **Theorem 5** (p. 14). Let `c ∈ (0, ∞)` and `k(n)/n → c`. If, for every `n ≥ 1`, the random
density matrix `ρₙ` has distribution `μ_{n,k(n)}`, then almost surely the renormalized empirical
distributions `Lₙ = (1/n) Σᵢ δ_{c n λᵢ(ρₙ)}` converge weakly to the Marchenko–Pastur law `μ_c`. -/
theorem theorem_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (c : ℝ) (hc : 0 < c) (k : ℕ → ℕ) (hk : ∀ n, 0 < n → 0 < k n)
    (hlim : Tendsto (fun n : ℕ => (k n : ℝ) / n) atTop (𝓝 c))
    (ρ : (n : ℕ) → Ω → Matrix (Fin n) (Fin n) ℂ)
    (hρ : ∀ n, 0 < n → HasInducedLaw P (ρ n) (k n)) :
    ∀ᵐ ω ∂P, ∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n : ℕ => ∫ x, f x ∂(esd (c * n) (ρ n ω))) atTop
        (𝓝 (∫ x, f x ∂(marchenkoPastur c))) := by sorry

end NechitaRDM.MP
