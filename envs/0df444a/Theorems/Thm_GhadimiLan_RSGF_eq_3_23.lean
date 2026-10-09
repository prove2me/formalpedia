-- Prove2me | Theorems.Thm_GhadimiLan_RSGF_eq_3_23
-- name    : GhadimiLan.RSGF.eq_3_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:20:39.134986+00:00
-- url     : https://prove2.me/theorems/b803cbba-9b75-44b8-9324-3e5d51d44da3
-- title:
--   (3.23), p. 18 — Σ[γ_k − 2L(n+4)γ_k²]E‖∇f(x_k)‖² ≤ 2[f(x_1) − f*] + 2L(n+4)σ²Σγ_k² + 2µ²L(n+4)[…]
-- statement:
--   Assume the hypotheses of Theorem 3.2 a), without the output index $R$:
--
--   - the standing assumptions of Section 3 with $L > 0$ and $\sigma \ge 0$;
--   - $f$ bounded below with infimum $f^*$;
--   - $N \ge 1$, $\mu > 0$, and stepsizes $0 < \gamma_k < 1/[2(n+4)L]$ for $k = 1,\dots,N$;
--   - a run $x_1, x_2, \dots$ of the RSGF method under the sampling model.
--
--   Then each $\|\nabla f(x_k)\|^2$, $k = 1,\dots,N$, is integrable and
--   $$
--   \begin{aligned}
--   \sum_{k=1}^N [\gamma_k - 2L(n+4)\gamma_k^2]\,\mathbb E\|\nabla f(x_k)\|^2
--   &\le 2[f(x_1)-f^*] + 2L(n+4)\sigma^2\sum_{k=1}^N\gamma_k^2 + 2\mu^2 L n + \frac{\mu^2}{2}L^2\sum_{k=1}^N\big[(n+3)^3\gamma_k + L(n+6)^3\gamma_k^2\big] \\
--   &\le 2[f(x_1)-f^*] + 2L(n+4)\sigma^2\sum_{k=1}^N\gamma_k^2 + 2\mu^2 L(n+4)\Big[1 + L(n+4)^2\sum_{k=1}^N\Big(\frac{\gamma_k}{4} + L\gamma_k^2\Big)\Big].
--   \end{aligned}
--   $$
--
--   This is the weighted bound on the expected squared gradient norms along the trajectory. Dividing by the total weight gives Theorem 3.2 a).
--
--   **Formalization Note** The chain is stated as two conjuncts: the left side is at most the middle line, and the middle line is at most the last. The smoothing parameter is `μs`.
-- source:
--   Ghadimi & Lan, arXiv:1309.5549v1, proof of Theorem 3.2, Eq. (3.23), p. 18

import Mathlib
import Definitions.Def_RandomGradFree_Shared_smoothing
import Definitions.Def_GhadimiLan_RSGF_Model
import Definitions.Def_GhadimiLan_RSGF_Method

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace GhadimiLan.RSGF

/-- Eq. (3.23), proof of Theorem 3.2 (Ghadimi & Lan, arXiv:1309.5549v1, p. 18). Under the
hypotheses of Theorem 3.2 a) (without the output index `R`): `f = objective P F` bounded below
with infimum `fstar`, `N ≥ 1`, `0 < γ_k < 1/[2(n+4)L]`, `μs > 0` (the paper's `µ`). Then each
`‖∇f(x_k)‖²`, `k = 1, …, N`, is integrable and, writing `w_k = γ_k − 2L(n+4)γ_k²`,
`Σ w_k E‖∇f(x_k)‖² ≤ 2[f(x_1) − f*] + 2L(n+4)σ² Σγ_k² + 2µ²Ln + (µ²/2) L² Σ[(n+3)³γ_k + L(n+6)³γ_k²]`
`≤ 2[f(x_1) − f*] + 2L(n+4)σ² Σγ_k² + 2µ²L(n+4)[1 + L(n+4)² Σ(γ_k/4 + Lγ_k²)]`. -/
theorem eq_3_23 {n : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure Ξ) [IsProbabilityMeasure P]
    (F : EuclideanSpace ℝ (Fin n) → Ξ → ℝ) (L σ μs : ℝ) (hL : 0 < L) (hσ : 0 ≤ σ) (hμs : 0 < μs)
    (hF : SZOAssumptions P F L σ) (γ : ℕ → ℝ)
    (ξ : ℕ → Ω → Ξ) (u : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (hs : IsSZOSampling μ P ξ u)
    (x1 : EuclideanSpace ℝ (Fin n)) (x : ℕ → Ω → EuclideanSpace ℝ (Fin n))
    (hx : IsRSGFRun F μs γ x1 ξ u x)
    (fstar : ℝ) (hfstar : IsGLB (Set.range (objective P F)) fstar)
    (N : ℕ) (hN : 1 ≤ N)
    (hγ : ∀ k ∈ Finset.Icc 1 N, 0 < γ k ∧ γ k < 1 / (2 * ((n : ℝ) + 4) * L)) :
    (∀ k ∈ Finset.Icc 1 N, Integrable (fun ω => ‖gradient (objective P F) (x k ω)‖ ^ 2) μ) ∧
      ∑ k ∈ Finset.Icc 1 N, (γ k - 2 * L * ((n : ℝ) + 4) * γ k ^ 2) *
          ∫ ω, ‖gradient (objective P F) (x k ω)‖ ^ 2 ∂μ ≤
        2 * (objective P F x1 - fstar) + 2 * L * ((n : ℝ) + 4) * σ ^ 2 * ∑ k ∈ Finset.Icc 1 N, γ k ^ 2
          + 2 * μs ^ 2 * L * (n : ℝ)
          + μs ^ 2 / 2 * L ^ 2 *
              ∑ k ∈ Finset.Icc 1 N, (((n : ℝ) + 3) ^ 3 * γ k + L * ((n : ℝ) + 6) ^ 3 * γ k ^ 2) ∧
      2 * (objective P F x1 - fstar) + 2 * L * ((n : ℝ) + 4) * σ ^ 2 * ∑ k ∈ Finset.Icc 1 N, γ k ^ 2
          + 2 * μs ^ 2 * L * (n : ℝ)
          + μs ^ 2 / 2 * L ^ 2 *
              ∑ k ∈ Finset.Icc 1 N, (((n : ℝ) + 3) ^ 3 * γ k + L * ((n : ℝ) + 6) ^ 3 * γ k ^ 2) ≤
        2 * (objective P F x1 - fstar) + 2 * L * ((n : ℝ) + 4) * σ ^ 2 * ∑ k ∈ Finset.Icc 1 N, γ k ^ 2
          + 2 * μs ^ 2 * L * ((n : ℝ) + 4) *
              (1 + L * ((n : ℝ) + 4) ^ 2 * ∑ k ∈ Finset.Icc 1 N, (γ k / 4 + L * γ k ^ 2)) := by sorry

end GhadimiLan.RSGF
