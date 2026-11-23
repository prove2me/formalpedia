-- Prove2me | Theorems.Thm_GlobalInexactNewton_Backtracking_Supplement_theorem_8_4
-- name    : GlobalInexactNewton.Backtracking.Supplement.theorem_8_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:03:24.172581+00:00
-- url     : https://prove2.me/theorems/d672fa4b-5cc3-40cf-a819-7344f4ad4575
-- title:
--   Theorem 8.4 — ECTL along residual-minimizing segments converges under the specified nonorthogonality condition, and eventually accepts the initial level.
-- statement:
--   Let Algorithm ECTL generate an infinite sequence $(x_k)$ with residual-minimizing equality curves constructed as on p. 416. Let $K_1(y)$ be the original first subspace chosen by the method at each point $y$, including stages skipped by a retained curve. Suppose $x_*$ is a limit point with invertible derivative and that the neighborhood nonorthogonality condition holds for $K_1$. Then
--
--   $$F(x_*)=0,\qquad x_k\to x_*,\qquad\eta_k=\bar\eta_k\ \text{eventually}.$$
--
--   This covers all nested residual-minimizing methods satisfying that condition and both truncation choices. ECTL has no uniform $\eta_{\max}<1$ restriction.
--
--   **Formalization Note** The paper states its results on $\mathbb R^n$; we use a finite-dimensional real space with exactly its specified norm and `ContDiff ℝ 1 F`. The paper states no breakdown and eventual initial-level acceptance; we state an infinite run and eventual equality with the published trial-level recurrence. All curve restrictions refer only to their stated level intervals.
--
--   Differences from the source:
--   - encoding: Real n-dimensional vectors, continuously differentiable F, and the paper’s algorithm or local data. → Finite-dimensional real normed spaces (inner product spaces in §§7–8), fderiv with ContDiff ℝ 1, and explicit data predicates.; reason: These are coordinate-independent representations with exactly the stated norm; a run on infinite sequences means no breakdown.
--   - reading: Limit point, sufficiently near and sufficiently large; no breakdown. → MapClusterPt; one positive neighborhood radius for any local uniform hypothesis; eventual equality of trialLevel and the initial level; infinite run predicates.; reason: This is the paper’s explicit limit-point and breakdown convention on p. 396, with neighborhood and eventual quantifiers written out.
-- source:
--   Eisenstat and Walker, Globally Convergent Inexact Newton Methods, SIAM J. Optim. 4(2) (1994), p. 417, Theorem 8.4; DOI 10.1137/0804022

import Mathlib
import Definitions.Def_GlobalInexactNewton_Backtracking_Method
import Definitions.Def_GlobalInexactNewton_Backtracking_Supplement_EqualityCurves
import Definitions.Def_GlobalInexactNewton_Backtracking_Supplement_ResidualCurve
import Definitions.Def_GlobalInexactNewton_Backtracking_Supplement_Nonorthogonality

namespace GlobalInexactNewton.Backtracking.Supplement

open Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem theorem_8_4 (F : E → E) (hF : ContDiff ℝ 1 F)
    (t u θmin θmax : ℝ) (x : ℕ → E) (ηbar : ℕ → ℝ)
    (σ : ℕ → ℝ → E) (θ : ℕ → ℕ → ℝ) (m : ℕ → ℕ)
    (K : E → ℕ → Submodule ℝ E) (z : ℕ → ℕ → E) (q : ℕ → ℕ → ℕ) (N : ℕ → ℕ)
    (hrun : IsECTLRun F t u θmin θmax x ηbar σ θ m)
    (hcurve : ∀ k, IsResidualCurve F (x k) (ηbar k) (σ k) (K (x k)) (z k) (q k) (N k))
    (xstar : E) (hcluster : MapClusterPt xstar atTop x)
    (hinv : (fderiv ℝ F xstar).IsInvertible)
    (hnonorth : Nonorthogonality F xstar (fun y => K y 1)) :
    F xstar = 0 ∧ Tendsto x atTop (𝓝 xstar) ∧
      ∀ᶠ k in atTop, trialLevel (ηbar k) (θ k) (m k) = ηbar k := by sorry

end GlobalInexactNewton.Backtracking.Supplement
