-- Prove2me | Theorems.Thm_GlobalInexactNewton_TrustRegion_theorem_4_4
-- name    : GlobalInexactNewton.TrustRegion.theorem_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:23:24.600626+00:00
-- url     : https://prove2.me/theorems/c7710c64-e4a8-43ea-8d7e-eae85d6c5ed9
-- title:
--   Theorem 4.4 — limit points of Algorithm TR are stationary points of ‖F‖; at one where F′ is invertible, F(x*) = 0, x_k → x* and full Newton steps are eventually taken
-- statement:
--   Let $E$ be a finite-dimensional real space with an arbitrary norm, let $F:E\to E$ be continuously differentiable, and consider a run of Algorithm TR (trust region method, p. 402) with parameters $\bar\delta_0>0$, $0<t\le u<1$, $0<\theta_{\min}<\theta_{\max}<1$, iterates $x_k$ and accepted steps $s_k$. Then:
--
--   1. every limit point of $(x_k)$ is a stationary point of $\|F\|$, i.e. $\|F(x_*)\|\le\|F(x_*)+F'(x_*)s\|$ for all $s$;
--   2. if $x_*$ is a limit point of $(x_k)$ such that $F'(x_*)$ is invertible, then $F(x_*)=0$ and $x_k\to x_*$; furthermore,
--   $$s_k=-F'(x_k)^{-1}F(x_k),$$
--   the full Newton step, whenever $k$ is sufficiently large.
--
--   This is the main result of the paper's Application 1: the inexact Newton framework yields global convergence of trust region methods for nonlinear equations under an arbitrary norm, with no assumption on bounded level sets or existence of a solution, and with eventual agreement with Newton's method near a regular solution.
--
--   **Formalization Note.** "Assume that Algorithm TR does not break down" is the hypothesis that a run exists (an infinite sequence of iterates, each while-loop ending after finitely many passes). "Limit point" is `MapClusterPt`. The first conclusion holds for every limit point, with no invertibility assumption. $F'(x_k)^{-1}$ is `(fderiv ℝ F (x k)).inverse`; it is the true inverse whenever $F'(x_k)$ is invertible, which holds for all large $k$ since $x_k\to x_*$ and invertibility is an open condition. "Whenever $k$ is sufficiently large" is `∀ᶠ k in atTop`.
-- source:
--   Eisenstat and Walker, Globally Convergent Inexact Newton Methods, SIAM J. Optim. 4(2) (1994), p. 405, Theorem 4.4

import Mathlib
import Definitions.Def_GlobalInexactNewton_TrustRegion_Method

namespace GlobalInexactNewton.TrustRegion

open Filter Topology

/-- Theorem 4.4, p. 405. -/
theorem theorem_4_4 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : E → E) (hF : ContDiff ℝ 1 F) (t u θmin θmax : ℝ) (x : ℕ → E) (δbar : ℕ → ℝ)
    (θ : ℕ → ℕ → ℝ) (m : ℕ → ℕ) (s : ℕ → ℕ → E)
    (hrun : IsTRRun F t u θmin θmax x δbar θ m s) :
    (∀ y : E, MapClusterPt y atTop x → IsStationaryPtNorm F y) ∧
      ∀ xstar : E, MapClusterPt xstar atTop x → (fderiv ℝ F xstar).IsInvertible →
        F xstar = 0 ∧ Tendsto x atTop (𝓝 xstar) ∧
          ∀ᶠ k in atTop, s k (m k) = -((fderiv ℝ F (x k)).inverse (F (x k))) := by sorry

end GlobalInexactNewton.TrustRegion
