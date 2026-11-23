-- Prove2me | Theorems.Thm_GlobalInexactNewton_Backtracking_Supplement_theorem_6_3
-- name    : GlobalInexactNewton.Backtracking.Supplement.theorem_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T08:50:42.412062+00:00
-- url     : https://prove2.me/theorems/9bccb433-7658-4469-8b5e-ea15300de630
-- title:
--   Theorem 6.3 — Piecewise linear inexact Newton backtracking converges at every invertible limit point and eventually accepts the initial level.
-- statement:
--   Consider Algorithm MR with the piecewise affine curves (6.2), initial levels $\bar\eta_k\in[0,\eta_{\max}]$ and $0\le\eta_{\max}<1$, under the paper's remaining parameter ranges. Assume it generates an infinite sequence $(x_k)$ and that $x_*$ is a limit point with invertible $F'(x_*)$. Then
--
--   $$F(x_*)=0,\qquad x_k\to x_*,\qquad\eta_k=\bar\eta_k\ \text{eventually}.$$
--
--   This extends the published backtracking convergence result to any finite list of admissible inexact Newton vertices. No equality of vertex residuals is required.
--
--   **Formalization Note** The paper states its results on $\mathbb R^n$; we use a finite-dimensional real space with exactly its specified norm and `ContDiff ℝ 1 F`. The paper states no breakdown and eventual initial-level acceptance; we state an infinite run and eventual equality with the published trial-level recurrence. All curve restrictions refer only to their stated level intervals.
--
--   Differences from the source:
--   - encoding: Real n-dimensional vectors, continuously differentiable F, and the paper’s algorithm or local data. → Finite-dimensional real normed spaces (inner product spaces in §§7–8), fderiv with ContDiff ℝ 1, and explicit data predicates.; reason: These are coordinate-independent representations with exactly the stated norm; a run on infinite sequences means no breakdown.
--   - reading: Limit point, sufficiently near and sufficiently large; no breakdown. → MapClusterPt; one positive neighborhood radius for any local uniform hypothesis; eventual equality of trialLevel and the initial level; infinite run predicates.; reason: This is the paper’s explicit limit-point and breakdown convention on p. 396, with neighborhood and eventual quantifiers written out.
-- source:
--   Eisenstat and Walker, Globally Convergent Inexact Newton Methods, SIAM J. Optim. 4(2) (1994), p. 411, Theorem 6.3; DOI 10.1137/0804022

import Mathlib
import Definitions.Def_GlobalInexactNewton_Backtracking_Method
import Definitions.Def_GlobalInexactNewton_Backtracking_Supplement_PiecewiseInexact

namespace GlobalInexactNewton.Backtracking.Supplement

open Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem theorem_6_3 (F : E → E) (hF : ContDiff ℝ 1 F)
    (ηmax t θmin θmax : ℝ) (x : ℕ → E) (ηbar : ℕ → ℝ)
    (σ : ℕ → ℝ → E) (θ : ℕ → ℕ → ℝ) (m : ℕ → ℕ)
    (hrun : IsMRRun F ηmax t θmin θmax x ηbar σ θ m)
    (hcurve : ∀ k, IsPiecewiseInexactCurve F (x k) ηmax (ηbar k) (σ k))
    (xstar : E) (hcluster : MapClusterPt xstar atTop x)
    (hinv : (fderiv ℝ F xstar).IsInvertible) :
    F xstar = 0 ∧ Tendsto x atTop (𝓝 xstar) ∧
      ∀ᶠ k in atTop, trialLevel (ηbar k) (θ k) (m k) = ηbar k := by sorry

end GlobalInexactNewton.Backtracking.Supplement
