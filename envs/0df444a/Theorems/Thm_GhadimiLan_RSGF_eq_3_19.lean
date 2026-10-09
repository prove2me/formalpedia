-- Prove2me | Theorems.Thm_GhadimiLan_RSGF_eq_3_19
-- name    : GhadimiLan.RSGF.eq_3_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:21:08.658376+00:00
-- url     : https://prove2.me/theorems/5b5245d4-2ab9-474d-8ee6-1dd6c464c331
-- title:
--   (3.18)–(3.19), p. 17 — the pathwise descent inequality for f_µ along an RSGF run
-- statement:
--   Assume the standing assumptions of Section 3 with $L > 0$, let $\mu > 0$, let $f_\mu$ be the Gaussian smoothing of $f$, and let $f_\mu^* = \inf_x f_\mu(x)$. Consider a run $x_1, x_2, \dots$ of the RSGF method with arbitrary stepsizes $\gamma_k$ and samples $\xi_k$, $u_k$. Write
--   $$
--   G_k = G_\mu(x_k,\xi_k,u_k), \qquad \Delta_k = G_k - \nabla f_\mu(x_k).
--   $$
--   Then for every outcome and every $N \ge 1$:
--
--   1. (3.18) for $k = 1,\dots,N$,
--   $$
--   f_\mu(x_{k+1}) \le f_\mu(x_k) - \gamma_k\|\nabla f_\mu(x_k)\|^2 - \gamma_k\langle \nabla f_\mu(x_k), \Delta_k\rangle + \frac{L}{2}\gamma_k^2 \|G_k\|^2 ;
--   $$
--   2. (3.19)
--   $$
--   \sum_{k=1}^N \gamma_k \|\nabla f_\mu(x_k)\|^2 \le f_\mu(x_1) - f_\mu^* - \sum_{k=1}^N \gamma_k \langle \nabla f_\mu(x_k), \Delta_k\rangle + \frac{L}{2}\sum_{k=1}^N \gamma_k^2 \|G_k\|^2 .
--   $$
--
--   This is the deterministic core of the proof of Theorem 3.2. Expectations of the last two sums are controlled by (3.20) and (3.21).
--
--   **Formalization Note** The statement holds sample path by sample path. It uses only that $f$, hence $f_\mu$, has an $L$-Lipschitz gradient. The smoothing parameter is `μs`.
-- source:
--   Ghadimi & Lan, arXiv:1309.5549v1, proof of Theorem 3.2, Eqs. (3.18)–(3.19), p. 17

import Mathlib
import Definitions.Def_RandomGradFree_Shared_smoothing
import Definitions.Def_GhadimiLan_RSGF_Model
import Definitions.Def_GhadimiLan_RSGF_Method

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace GhadimiLan.RSGF

/-- Eqs. (3.18)–(3.19), proof of Theorem 3.2 (Ghadimi & Lan, arXiv:1309.5549v1, p. 17), pathwise.
Write `f = objective P F`, `f_µ` for its Gaussian smoothing with parameter `μs > 0` (the paper's
`µ`), `f*_µ = fμstar` for the infimum of `f_µ`, `G_k = G_µ(x_k, ξ_k, u_k)` and
`Δ_k = G_k − ∇f_µ(x_k)`. For every outcome `ω` of a run of the RSGF method:
(3.18) for `k = 1, …, N`,
`f_µ(x_{k+1}) ≤ f_µ(x_k) − γ_k‖∇f_µ(x_k)‖² − γ_k⟨∇f_µ(x_k), Δ_k⟩ + (L/2)γ_k²‖G_k‖²`; and
(3.19) `Σ_{k=1}^N γ_k‖∇f_µ(x_k)‖² ≤ f_µ(x_1) − f*_µ − Σ_{k=1}^N γ_k⟨∇f_µ(x_k), Δ_k⟩ + (L/2)Σ_{k=1}^N γ_k²‖G_k‖²`. -/
theorem eq_3_19 {n : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ξ] (P : Measure Ξ) [IsProbabilityMeasure P]
    (F : EuclideanSpace ℝ (Fin n) → Ξ → ℝ) (L σ μs : ℝ) (hL : 0 < L) (hμs : 0 < μs)
    (hF : SZOAssumptions P F L σ)
    (fμstar : ℝ)
    (hfμstar : IsGLB (Set.range (RandomGradFree.Shared.smoothing (objective P F) μs)) fμstar)
    (N : ℕ) (hN : 1 ≤ N) (γ : ℕ → ℝ)
    (ξ : ℕ → Ω → Ξ) (u : ℕ → Ω → EuclideanSpace ℝ (Fin n))
    (x1 : EuclideanSpace ℝ (Fin n)) (x : ℕ → Ω → EuclideanSpace ℝ (Fin n))
    (hx : IsRSGFRun F μs γ x1 ξ u x) (ω : Ω) :
    (∀ k ∈ Finset.Icc 1 N,
      RandomGradFree.Shared.smoothing (objective P F) μs (x (k + 1) ω) ≤
        RandomGradFree.Shared.smoothing (objective P F) μs (x k ω)
          - γ k * ‖gradient (RandomGradFree.Shared.smoothing (objective P F) μs) (x k ω)‖ ^ 2
          - γ k * ⟪gradient (RandomGradFree.Shared.smoothing (objective P F) μs) (x k ω),
              szoGrad F μs (x k ω) (ξ k ω) (u k ω)
                - gradient (RandomGradFree.Shared.smoothing (objective P F) μs) (x k ω)⟫_ℝ
          + L / 2 * γ k ^ 2 * ‖szoGrad F μs (x k ω) (ξ k ω) (u k ω)‖ ^ 2) ∧
    ∑ k ∈ Finset.Icc 1 N,
        γ k * ‖gradient (RandomGradFree.Shared.smoothing (objective P F) μs) (x k ω)‖ ^ 2 ≤
      RandomGradFree.Shared.smoothing (objective P F) μs x1 - fμstar
        - ∑ k ∈ Finset.Icc 1 N,
            γ k * ⟪gradient (RandomGradFree.Shared.smoothing (objective P F) μs) (x k ω),
              szoGrad F μs (x k ω) (ξ k ω) (u k ω)
                - gradient (RandomGradFree.Shared.smoothing (objective P F) μs) (x k ω)⟫_ℝ
        + L / 2 * ∑ k ∈ Finset.Icc 1 N,
            γ k ^ 2 * ‖szoGrad F μs (x k ω) (ξ k ω) (u k ω)‖ ^ 2 := by sorry

end GhadimiLan.RSGF
