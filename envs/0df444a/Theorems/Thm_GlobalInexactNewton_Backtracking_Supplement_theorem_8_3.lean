-- Prove2me | Theorems.Thm_GlobalInexactNewton_Backtracking_Supplement_theorem_8_3
-- name    : GlobalInexactNewton.Backtracking.Supplement.theorem_8_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:00:51.917807+00:00
-- url     : https://prove2.me/theorems/6ff8db3b-9d9f-49c7-897b-b656ed91c64e
-- title:
--   Theorem 8.3 — ECMR along residual-minimizing segments converges under the first-segment bound η_k⁽¹⁾ ≤ η_max, and eventually accepts the initial level.
-- statement:
--   Let Algorithm ECMR generate an infinite sequence $(x_k)$, with its curves constructed from arbitrary nested-subspace residual minimizers as on p. 416, including skipped stages and either final-endpoint convention. Assume that the first retained vertex level, after any final truncation, satisfies $\eta_k^{(1)}\le\eta_{\max}$ whenever $F(x_k)\ne0$. If $x_*$ is a limit point with invertible derivative, then
--
--   $$F(x_*)=0,\qquad x_k\to x_*,\qquad\eta_k=\bar\eta_k\ \text{eventually}.$$
--
--   The first-vertex bound is separate from ECMR's initial-level bound. No particular residual-minimizing method or matrix rank is assumed.
--
--   **Formalization Note** The paper states its results on $\mathbb R^n$; we use a finite-dimensional real space with exactly its specified norm and `ContDiff ℝ 1 F`. The paper states no breakdown and eventual initial-level acceptance; we state an infinite run and eventual equality with the published trial-level recurrence. All curve restrictions refer only to their stated level intervals.
--
--   Differences from the source:
--   - encoding: Real n-dimensional vectors, continuously differentiable F, and the paper’s algorithm or local data. → Finite-dimensional real normed spaces (inner product spaces in §§7–8), fderiv with ContDiff ℝ 1, and explicit data predicates.; reason: These are coordinate-independent representations with exactly the stated norm; a run on infinite sequences means no breakdown.
--   - reading: Limit point, sufficiently near and sufficiently large; no breakdown. → MapClusterPt; one positive neighborhood radius for any local uniform hypothesis; eventual equality of trialLevel and the initial level; infinite run predicates.; reason: This is the paper’s explicit limit-point and breakdown convention on p. 396, with neighborhood and eventual quantifiers written out.
-- source:
--   Eisenstat and Walker, Globally Convergent Inexact Newton Methods, SIAM J. Optim. 4(2) (1994), p. 417, Theorem 8.3; DOI 10.1137/0804022

import Mathlib
import Definitions.Def_GlobalInexactNewton_Backtracking_Method
import Definitions.Def_GlobalInexactNewton_Backtracking_Supplement_EqualityCurves
import Definitions.Def_GlobalInexactNewton_Backtracking_Supplement_ResidualCurve

namespace GlobalInexactNewton.Backtracking.Supplement

open Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem theorem_8_3 (F : E → E) (hF : ContDiff ℝ 1 F)
    (ηmax t θmin θmax : ℝ) (x : ℕ → E) (ηbar : ℕ → ℝ)
    (σ : ℕ → ℝ → E) (θ : ℕ → ℕ → ℝ) (m : ℕ → ℕ)
    (K : ℕ → ℕ → Submodule ℝ E) (z : ℕ → ℕ → E) (q : ℕ → ℕ → ℕ) (N : ℕ → ℕ)
    (hrun : IsECMRRun F ηmax t θmin θmax x ηbar σ θ m)
    (hcurve : ∀ k, IsResidualCurve F (x k) (ηbar k) (σ k) (K k) (z k) (q k) (N k))
    (hfirst : ∀ k, F (x k) ≠ 0 → firstVertexLevel F (x k) (ηbar k) (z k) (q k) ≤ ηmax)
    (xstar : E) (hcluster : MapClusterPt xstar atTop x)
    (hinv : (fderiv ℝ F xstar).IsInvertible) :
    F xstar = 0 ∧ Tendsto x atTop (𝓝 xstar) ∧
      ∀ᶠ k in atTop, trialLevel (ηbar k) (θ k) (m k) = ηbar k := by sorry

end GlobalInexactNewton.Backtracking.Supplement
