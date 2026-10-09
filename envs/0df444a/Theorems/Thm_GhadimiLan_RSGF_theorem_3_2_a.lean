-- Prove2me | Theorems.Thm_GhadimiLan_RSGF_theorem_3_2_a
-- name    : GhadimiLan.RSGF.theorem_3_2_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:20:47.958321+00:00
-- url     : https://prove2.me/theorems/7fa8c7bc-0cc9-4a04-9d06-f30beb3023b2
-- title:
--   Theorem 3.2 a), (3.16), p. 17 — the RSGF method bounds (1/L)E‖∇f(x_R)‖² for nonconvex f
-- statement:
--   Consider the stochastic program $f^* = \inf_{x\in\mathbb R^n} \{ f(x) := \mathbb E[F(x,\xi)] \}$ (3.1), where $\xi \sim P$. Assume:
--
--   1. $F(\cdot,\xi) \in \mathcal C^{1,1}_L(\mathbb R^n)$ almost surely, with $L > 0$;
--   2. Assumption A1 for $G(x,\xi) = \nabla_x F(x,\xi)$, with variance bound $\sigma^2$;
--   3. Assumption A3;
--   4. $f$ is bounded below.
--
--   Run the randomized stochastic gradient free (RSGF) method (3.12)–(3.13) from $x_1$. It uses smoothing parameter $\mu > 0$, iteration limit $N \ge 1$, and stepsizes with $0 < \gamma_k < 1/[2(n+4)L]$. At each step it draws a fresh sample $\xi_k$ and a fresh standard Gaussian direction $u_k$, all mutually independent. Its output is $x_R$, where the random index $R$ is independent of the samples and has probability mass function
--   $$
--   P_R(k) = \frac{\gamma_k - 2L(n+4)\gamma_k^2}{\sum_{j=1}^N [\gamma_j - 2L(n+4)\gamma_j^2]}, \qquad k = 1,\dots,N. \tag{3.15}
--   $$
--   Then $\|\nabla f(x_R)\|^2$ is integrable and
--   $$
--   \frac1L\,\mathbb E\big[\|\nabla f(x_R)\|^2\big] \le \frac{1}{\sum_{k=1}^N [\gamma_k - 2L(n+4)\gamma_k^2]}\Big[D_f^2 + 2\mu^2(n+4)\Big(1 + L(n+4)^2\sum_{k=1}^N\Big(\frac{\gamma_k}{4} + L\gamma_k^2\Big)\Big) + 2(n+4)\sigma^2\sum_{k=1}^N\gamma_k^2\Big],
--   $$
--   where $D_f^2 = 2(f(x_1)-f^*)/L$ (2.5), and the expectation is over $R$, $\xi_{[N]}$ and $u_{[N]}$.
--
--   This is the main convergence guarantee of the paper for nonconvex stochastic optimization with zeroth-order (function value) information only. With constant stepsizes it gives the $O(n/\epsilon^2)$ complexity of Corollary 3.3.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`, and the constants $(n+4)$ use the same $n$. The smoothing parameter $\mu$ is `μs`, and `μ` is the probability measure. The value $f^*$ is the infimum of $f$ (`IsGLB`), and $D_f^2$ is written out as $2(f(x_1)-f^*)/L$. The following are disclosed additions that make the paper's implicit setting explicit:
--
--   - the samples are measurable and mutually independent, and $R$ is independent of them;
--   - $F$ is jointly measurable and $F(x,\cdot)$, $\nabla_xF(x,\cdot)$ are integrable;
--   - the stepsizes are positive.
--
--   The integrability of $\|\nabla f(x_R)\|^2$ is part of the conclusion.
-- source:
--   Ghadimi & Lan, arXiv:1309.5549v1, Theorem 3.2 a), Eqs. (3.15)–(3.16), pp. 16–17; D_f from Eq. (2.5), p. 6

import Mathlib
import Definitions.Def_GhadimiLan_RSGF_Model
import Definitions.Def_GhadimiLan_RSGF_Method

open MeasureTheory ProbabilityTheory

namespace GhadimiLan.RSGF

/-- Theorem 3.2 a), Eq. (3.16) (Ghadimi & Lan, arXiv:1309.5549v1, pp. 16–17). Under the standing
assumptions of §3 (A1 for `G = ∇_x F`, A3, `F(·, ξ) ∈ C^{1,1}_L` a.s.), with `f = objective P F`
bounded below with infimum `fstar`, stepsizes `0 < γ_k < 1/[2(n+4)L]`, smoothing parameter
`μs > 0` (the paper's `µ`; `μ` is the probability measure) and the random output index `R` with
the pmf (3.15), drawn independently of the samples, the RSGF output satisfies
`(1/L) E‖∇f(x_R)‖² ≤ [D_f² + 2µ²(n+4)(1 + L(n+4)² Σ(γ_k/4 + Lγ_k²)) + 2(n+4)σ² Σγ_k²] / Σ[γ_k − 2L(n+4)γ_k²]`
with `D_f² = 2(f(x_1) − f*)/L` (2.5). The integrability of `‖∇f(x_R)‖²` is part of the claim. -/
theorem theorem_3_2_a {n : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure Ξ) [IsProbabilityMeasure P]
    (F : EuclideanSpace ℝ (Fin n) → Ξ → ℝ) (L σ μs : ℝ) (hL : 0 < L) (hσ : 0 ≤ σ) (hμs : 0 < μs)
    (hF : SZOAssumptions P F L σ)
    (fstar : ℝ) (hfstar : IsGLB (Set.range (objective P F)) fstar)
    (N : ℕ) (hN : 1 ≤ N) (γ : ℕ → ℝ)
    (hγ : ∀ k ∈ Finset.Icc 1 N, 0 < γ k ∧ γ k < 1 / (2 * ((n : ℝ) + 4) * L))
    (ξ : ℕ → Ω → Ξ) (u : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (hs : IsSZOSampling μ P ξ u)
    (x1 : EuclideanSpace ℝ (Fin n)) (x : ℕ → Ω → EuclideanSpace ℝ (Fin n))
    (hx : IsRSGFRun F μs γ x1 ξ u x)
    (R : Ω → ℕ) (hR : IsOutputIndex μ ξ u N (rsgfPMF L n γ N) R) :
    Integrable (fun ω => ‖gradient (objective P F) (x (R ω) ω)‖ ^ 2) μ ∧
      1 / L * ∫ ω, ‖gradient (objective P F) (x (R ω) ω)‖ ^ 2 ∂μ ≤
        1 / (∑ k ∈ Finset.Icc 1 N, (γ k - 2 * L * ((n : ℝ) + 4) * γ k ^ 2)) *
          (2 * (objective P F x1 - fstar) / L
            + 2 * μs ^ 2 * ((n : ℝ) + 4) *
                (1 + L * ((n : ℝ) + 4) ^ 2 * ∑ k ∈ Finset.Icc 1 N, (γ k / 4 + L * γ k ^ 2))
            + 2 * ((n : ℝ) + 4) * σ ^ 2 * ∑ k ∈ Finset.Icc 1 N, γ k ^ 2) := by sorry

end GhadimiLan.RSGF
