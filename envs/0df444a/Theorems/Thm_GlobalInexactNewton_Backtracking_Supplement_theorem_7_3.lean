-- Prove2me | Theorems.Thm_GlobalInexactNewton_Backtracking_Supplement_theorem_7_3
-- name    : GlobalInexactNewton.Backtracking.Supplement.theorem_7_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T08:56:34.490798+00:00
-- url     : https://prove2.me/theorems/604ac9ed-b0c5-490f-873d-d148dd6bb3f2
-- title:
--   Theorem 7.3 — For both ECMR and ECTL, a uniform positive curve angle near an invertible limit point gives a zero, convergence and eventual initial-level acceptance.
-- statement:
--   Let either Algorithm ECMR or Algorithm ECTL generate an infinite sequence $(x_k)$ using continuous equality curves $\sigma_k$. Suppose $x_*$ is a limit point with invertible derivative. Suppose a single $\gamma>0$ bounds the curve angle below whenever $F(x_k)\ne0$ and $x_k$ lies in one fixed neighborhood of $x_*$. Then
--
--   $$F(x_*)=0,\qquad x_k\to x_*,\qquad\eta_k=\bar\eta_k\ \text{eventually}.$$
--
--   Both algorithms and all three conclusions are included. This specializes the published MR/TL convergence theory to equality curves.
--
--   **Formalization Note** The paper states its results on $\mathbb R^n$; we use a finite-dimensional real space with exactly its specified norm and `ContDiff ℝ 1 F`. The paper states no breakdown and eventual initial-level acceptance; we state an infinite run and eventual equality with the published trial-level recurrence. All curve restrictions refer only to their stated level intervals.
--
--   Differences from the source:
--   - encoding: Real n-dimensional vectors, continuously differentiable F, and the paper’s algorithm or local data. → Finite-dimensional real normed spaces (inner product spaces in §§7–8), fderiv with ContDiff ℝ 1, and explicit data predicates.; reason: These are coordinate-independent representations with exactly the stated norm; a run on infinite sequences means no breakdown.
--   - reading: Limit point, sufficiently near and sufficiently large; no breakdown. → MapClusterPt; one positive neighborhood radius for any local uniform hypothesis; eventual equality of trialLevel and the initial level; infinite run predicates.; reason: This is the paper’s explicit limit-point and breakdown convention on p. 396, with neighborhood and eventual quantifiers written out.
--   - encoding: The lower bound in (7.7) is stated for an infimum over the half-open level interval. → UniformCurveAngle bounds every angle on that interval, with one positive constant and one positive neighborhood radius.; reason: Run level bounds make the interval nonempty; Cauchy–Schwarz bounds its angles in [0,1]. A lower bound on its real infimum is therefore equivalent to the pointwise bound.
-- source:
--   Eisenstat and Walker, Globally Convergent Inexact Newton Methods, SIAM J. Optim. 4(2) (1994), p. 415, Theorem 7.3; DOI 10.1137/0804022

import Mathlib
import Definitions.Def_GlobalInexactNewton_Backtracking_Method
import Definitions.Def_GlobalInexactNewton_Backtracking_Supplement_EqualityCurves

namespace GlobalInexactNewton.Backtracking.Supplement

open Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem theorem_7_3 (F : E → E) (hF : ContDiff ℝ 1 F)
    (ηmax t u θmin θmax : ℝ) (x : ℕ → E) (ηbar : ℕ → ℝ)
    (σ : ℕ → ℝ → E) (θ : ℕ → ℕ → ℝ) (m : ℕ → ℕ)
    (hrun : IsECMRRun F ηmax t θmin θmax x ηbar σ θ m ∨
      IsECTLRun F t u θmin θmax x ηbar σ θ m)
    (xstar : E) (hcluster : MapClusterPt xstar atTop x)
    (hinv : (fderiv ℝ F xstar).IsInvertible)
    (hangle : UniformCurveAngle F xstar x ηbar σ) :
    F xstar = 0 ∧ Tendsto x atTop (𝓝 xstar) ∧
      ∀ᶠ k in atTop, trialLevel (ηbar k) (θ k) (m k) = ηbar k := by sorry

end GlobalInexactNewton.Backtracking.Supplement
