-- Prove2me | Theorems.Thm_ImpulsiveISS_SmallGain_eta_lt_id
-- name    : ImpulsiveISS.SmallGain.eta_lt_id
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:57:19.787609+00:00
-- url     : https://prove2.me/theorems/c6e60774-5c72-44d4-a12e-ed5ed7d722e7
-- title:
--   Proof of Theorem 8, p. 20 — by (4.8), $\eta=\max_{i,j\ne i}\sigma_i^{-1}\circ\chi_{ij}\circ\sigma_j<\mathrm{id}$
-- statement:
--   Let $\chi_{ij}:\mathbb R_+\to\mathbb R_+$ ($i,j=1,\dots,n$) be gains, $\Gamma$ the gain operator $\Gamma(s)_i=\max_j\chi_{ij}(s_j)$ of (4.7), and $\sigma$ an $\Omega$-path for $\Gamma$ with inverses $\sigma_i^{-1}$, so that in particular $\Gamma(\sigma(r))<\sigma(r)$ in every component for $r>0$ (4.8). Then the function
--   $$\eta(r)=\max_{i,\ j\ne i}\ \sigma_i^{-1}\big(\chi_{ij}(\sigma_j(r))\big)$$
--   satisfies
--   $$\eta(r)<r\qquad\text{for every } r>0.$$
--
--   In the proof of Theorem 8, $\eta$ bounds the contribution of the interconnection gains to the jump of $V$.
--
--   **Formalization Note** For $n\le1$ there is no pair $j\ne i$ and $\eta$ is the empty maximum $0$, so the claim holds trivially; for $n\ge2$ it is the content of the page's display. At $r=0$ both sides are $0$, which is why the statement is for $r>0$.
-- source:
--   Dashkovskiy and Mironchenko, Input-to-state stability of nonlinear impulsive systems, arXiv:1212.5481v1, p. 20, proof of Theorem 8, display after 'Define also η'

import Mathlib
import Definitions.Def_SmallGainISS_Lyapunov_Gains
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_DiniDerivative
import Definitions.Def_ImpulsiveISS_SmallGain_System
import Definitions.Def_ImpulsiveISS_SmallGain_Interconnection
open scoped NNReal
open SmallGainISS.Lyapunov ProcessingNetworks.LyapunovCriteria

namespace ImpulsiveISS.SmallGain

/-- Proof of Theorem 8 (arXiv:1212.5481v1, p. 20), by (4.8): if `σ` is an Ω-path for the gain
operator `Γ` of (4.7) (with `τᵢ = σᵢ⁻¹`), then `η = max_{i, j ≠ i} σᵢ⁻¹ ∘ χᵢⱼ ∘ σⱼ` satisfies
`η(r) < r` for every `r > 0`. -/
theorem eta_lt_id {n : ℕ} (χ : Fin n → Fin n → ℝ≥0 → ℝ≥0)
    (σ : ℝ≥0 → Fin n → ℝ≥0) (τ : Fin n → ℝ≥0 → ℝ≥0) (hσ : IsOmegaPath (gainOp χ) σ τ) :
    ∀ r : ℝ≥0, 0 < r → etaGain σ τ χ r < r := by sorry

end ImpulsiveISS.SmallGain
