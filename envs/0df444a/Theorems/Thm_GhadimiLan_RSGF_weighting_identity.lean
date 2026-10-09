-- Prove2me | Theorems.Thm_GhadimiLan_RSGF_weighting_identity
-- name    : GhadimiLan.RSGF.weighting_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:20:55.282589+00:00
-- url     : https://prove2.me/theorems/a59a8117-ee2f-4f79-a645-b38a4d9219d2
-- title:
--   Proof of Theorem 3.2, p. 18 — E‖∇f(x_R)‖² = Σ[γ_k − 2L(n+4)γ_k²]E‖∇f(x_k)‖² / Σ[γ_k − 2L(n+4)γ_k²]
-- statement:
--   Assume the hypotheses of Theorem 3.2 a). These are the standing assumptions of Section 3 with $L > 0$, $\sigma \ge 0$, $N \ge 1$, $\mu > 0$, stepsizes $0 < \gamma_k < 1/[2(n+4)L]$, and a run of the RSGF method under the sampling model. In addition, let the output index $R$ have the probability mass function (3.15) and be independent of the samples $(\xi_k,u_k)_k$. Then $\|\nabla f(x_R)\|^2$ is integrable and
--   $$
--   \mathbb E\|\nabla f(x_R)\|^2 = \frac{\sum_{k=1}^N [\gamma_k - 2L(n+4)\gamma_k^2]\,\mathbb E\|\nabla f(x_k)\|^2}{\sum_{k=1}^N [\gamma_k - 2L(n+4)\gamma_k^2]} .
--   $$
--
--   Because $R$ is independent of the trajectory, the expectation at the random output is the $P_R$-weighted average of the expectations along the trajectory. This identity links (3.23) to the goal (3.16).
--
--   **Formalization Note** The independence of $R$ from the samples is implicit in the paper ("the expectation is taken with respect to $R$, $\xi_{[N]}$ and $u_{[N]}$") and is part of the model. The smoothing parameter is `μs`.
-- source:
--   Ghadimi & Lan, arXiv:1309.5549v1, proof of Theorem 3.2, display after "Dividing both sides", p. 18

import Mathlib
import Definitions.Def_RandomGradFree_Shared_smoothing
import Definitions.Def_GhadimiLan_RSGF_Model
import Definitions.Def_GhadimiLan_RSGF_Method

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace GhadimiLan.RSGF

/-- The `R`-weighting identity in the proof of Theorem 3.2 (Ghadimi & Lan, arXiv:1309.5549v1,
p. 18, display after "Dividing both sides"). Under the hypotheses of Theorem 3.2 a), with the
output index `R` of pmf (3.15) drawn independently of the samples, `‖∇f(x_R)‖²` is integrable and
`E‖∇f(x_R)‖² = Σ_{k=1}^N [γ_k − 2L(n+4)γ_k²] E‖∇f(x_k)‖² / Σ_{k=1}^N [γ_k − 2L(n+4)γ_k²]`. -/
theorem weighting_identity {n : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure Ξ) [IsProbabilityMeasure P]
    (F : EuclideanSpace ℝ (Fin n) → Ξ → ℝ) (L σ μs : ℝ) (hL : 0 < L) (hσ : 0 ≤ σ) (hμs : 0 < μs)
    (hF : SZOAssumptions P F L σ) (γ : ℕ → ℝ)
    (ξ : ℕ → Ω → Ξ) (u : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (hs : IsSZOSampling μ P ξ u)
    (x1 : EuclideanSpace ℝ (Fin n)) (x : ℕ → Ω → EuclideanSpace ℝ (Fin n))
    (hx : IsRSGFRun F μs γ x1 ξ u x)
    (N : ℕ) (hN : 1 ≤ N)
    (hγ : ∀ k ∈ Finset.Icc 1 N, 0 < γ k ∧ γ k < 1 / (2 * ((n : ℝ) + 4) * L))
    (R : Ω → ℕ) (hR : IsOutputIndex μ ξ u N (rsgfPMF L n γ N) R) :
    Integrable (fun ω => ‖gradient (objective P F) (x (R ω) ω)‖ ^ 2) μ ∧
      ∫ ω, ‖gradient (objective P F) (x (R ω) ω)‖ ^ 2 ∂μ =
        (∑ k ∈ Finset.Icc 1 N, (γ k - 2 * L * ((n : ℝ) + 4) * γ k ^ 2) *
            ∫ ω, ‖gradient (objective P F) (x k ω)‖ ^ 2 ∂μ) /
          ∑ k ∈ Finset.Icc 1 N, (γ k - 2 * L * ((n : ℝ) + 4) * γ k ^ 2) := by sorry

end GhadimiLan.RSGF
