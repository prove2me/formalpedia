-- Prove2me | Theorems.Thm_LinearMDPRL_Linear_lemma_D_4
-- name    : LinearMDPRL.Linear.lemma_D_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:41:22.196626+00:00
-- url     : https://prove2.me/theorems/dc45e40d-f5d7-4906-ba47-c312ee32c622
-- title:
--   Lemma D.4, p. 27 — uniform self-normalized bound over a value class with an ε-cover N_ε
-- statement:
--   Let $(x_\tau)_{\tau\ge1}$ be a stochastic process on the state space $\mathcal S$ adapted to a filtration $(\mathcal F_\tau)_{\tau\ge0}$, and let $(\phi_\tau)_{\tau\ge1}$ be an $\mathbb R^d$-valued process with $\phi_\tau$ $\mathcal F_{\tau-1}$-measurable and $\|\phi_\tau\|\le1$. Let $\lambda>0$ and $\Lambda_k=\lambda I+\sum_{\tau=1}^k\phi_\tau\phi_\tau^\top$. Let $\mathcal V$ be a class of measurable functions with $\sup_x|V(x)|\le H$ for all $V\in\mathcal V$, let $\varepsilon>0$, and let $\mathcal N\subseteq\mathcal V$ be a finite $\varepsilon$-cover of $\mathcal V$ in $\mathrm{dist}(V,V')=\sup_x|V(x)-V'(x)|$. Then for any $\delta>0$, with probability at least $1-\delta$, for all $k\ge0$ and all $V\in\mathcal V$,
--   $$
--   \Big\|\sum_{\tau=1}^k\phi_\tau\big\{V(x_\tau)-\mathbb E[V(x_\tau)\mid\mathcal F_{\tau-1}]\big\}\Big\|^2_{\Lambda_k^{-1}}\le 4H^2\Big[\frac d2\log\Big(\frac{k+\lambda}{\lambda}\Big)+\log\frac{|\mathcal N|}{\delta}\Big]+\frac{8k^2\varepsilon^2}{\lambda}.
--   $$
--
--   This is the uniform-over-$\mathcal V$ version of the self-normalized bound for vector-valued martingales (Theorem D.3); it is what makes it possible to use the data-dependent value estimates $V^k_{h+1}$ as regression targets.
--
--   **Formalization Note.** The conditional expectation is represented directly by Mathlib’s conditional expectation of $V\circ x_\tau$ given $\mathcal F_{\tau-1}$. The paper's $\mathcal N_\varepsilon$ is the $\varepsilon$-covering number; the statement is made for every finite $\varepsilon$-cover whose centers lie in $\mathcal V$, which is the form the proof uses (it applies Theorem D.3 to the centers, which therefore must be bounded by $H$ and measurable). "With probability at least $1-\delta$" is written as an upper bound $\delta$ on the outer measure of the failure set.
-- source:
--   Jin, Yang, Wang, Jordan, arXiv:1907.05388v2, Lemma D.4, p. 27

import Mathlib

namespace LinearMDPRL.Linear

open MeasureTheory ProbabilityTheory Matrix

/-- **Lemma D.4** (arXiv:1907.05388v2, p. 27). Let `(x_τ)_{τ ≥ 1}` be a stochastic process on the
state space `S` adapted to the filtration `(𝓕_τ)_{τ ≥ 0}`, and let `(φ_τ)_{τ ≥ 1}` be an
`ℝ^d`-valued process with `φ_τ` `𝓕_{τ−1}`-measurable and `‖φ_τ‖ ≤ 1`. Let
`Λ_k = λI + Σ_{τ=1}^k φ_τ φ_τ^⊤`. Let `𝒱` be a class of measurable functions with
`sup_x |V(x)| ≤ H`, and `N ⊆ 𝒱` a finite `ε`-cover of `𝒱` in `dist(V, V') = sup_x |V(x) − V'(x)|`.
Then for any `δ > 0`, with probability at least `1 − δ`, for all `k ≥ 0` and all `V ∈ 𝒱`,
`‖Σ_{τ=1}^k φ_τ {V(x_τ) − E[V(x_τ) | 𝓕_{τ−1}]}‖²_{Λ_k^{-1}}
  ≤ 4H² [d/2 · log((k + λ)/λ) + log(|N|/δ)] + 8k²ε²/λ`.

The conditional expectation is Mathlib's `μ[V ∘ x_τ | 𝓕_{τ−1}]`. -/
theorem lemma_D_4 {S : Type*} [MeasurableSpace S] {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›) (d : ℕ)
    (xs : ℕ → Ω → S) (hx : ∀ τ, 1 ≤ τ → Measurable[𝓕 τ] (xs τ))
    (φs : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hφ : ∀ τ, 1 ≤ τ → Measurable[𝓕 (τ - 1)] (φs τ)) (hφ1 : ∀ τ ω, ‖φs τ ω‖ ≤ 1)
    (lam : ℝ) (hlam : 0 < lam) (H : ℝ) (𝒱 : Set (S → ℝ))
    (h𝒱meas : ∀ V ∈ 𝒱, Measurable V) (h𝒱 : ∀ V ∈ 𝒱, ∀ x, |V x| ≤ H)
    (ε : ℝ) (hε : 0 < ε) (N : Finset (S → ℝ)) (hN𝒱 : ∀ V ∈ N, V ∈ 𝒱)
    (hN : ∀ V ∈ 𝒱, ∃ V' ∈ N, ∀ x, |V x - V' x| ≤ ε) (δ : ℝ) (hδ : 0 < δ) :
    μ {ω | ∃ k : ℕ, ∃ V ∈ 𝒱,
        let Λ : Matrix (Fin d) (Fin d) ℝ := lam • (1 : Matrix (Fin d) (Fin d) ℝ) +
          ∑ τ ∈ Finset.Icc 1 k, vecMulVec (WithLp.ofLp (φs τ ω)) (WithLp.ofLp (φs τ ω))
        let s : Fin d → ℝ := ∑ τ ∈ Finset.Icc 1 k,
          (V (xs τ ω) - μ[fun ω' => V (xs τ ω') | 𝓕 (τ - 1)] ω) •
            WithLp.ofLp (φs τ ω)
        4 * H ^ 2 * ((d : ℝ) / 2 * Real.log ((k + lam) / lam) + Real.log (N.card / δ)) +
            8 * (k : ℝ) ^ 2 * ε ^ 2 / lam < s ⬝ᵥ (Λ⁻¹ *ᵥ s)}
      ≤ ENNReal.ofReal δ := by sorry

end LinearMDPRL.Linear
