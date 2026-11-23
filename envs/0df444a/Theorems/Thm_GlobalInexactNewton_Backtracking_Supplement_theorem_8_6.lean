-- Prove2me | Theorems.Thm_GlobalInexactNewton_Backtracking_Supplement_theorem_8_6
-- name    : GlobalInexactNewton.Backtracking.Supplement.theorem_8_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:04:08.227552+00:00
-- url     : https://prove2.me/theorems/fcd923e0-a8bd-41af-b3a4-0a853746dd82
-- title:
--   Theorem 8.6 — ECMR and ECTL with Levenberg–Marquardt curves (corrected: singular and zero-residual endpoints)
-- statement:
--   Let either Algorithm ECMR or Algorithm ECTL generate an infinite sequence $(x_k)$ using subcurves of the Euclidean Levenberg–Marquardt curve, parametrized by residual level as in (7.1). If $x_*$ is a limit point with invertible $F'(x_*)$, then
--
--   $$F(x_*)=0,\qquad x_k\to x_*,\qquad\eta_k=\bar\eta_k\ \text{eventually}.$$
--
--   This includes both algorithms, all their permitted initial levels, zero-residual iterates, and earlier singular derivatives whenever the chosen subcurves exist. Positive damping and its attained endpoint limits specify the curve without a total inverse at a singular point.
--
--   **Formalization Note** The paper states its results on $\mathbb R^n$; we use a finite-dimensional real space with exactly its specified norm and `ContDiff ℝ 1 F`. The paper states no breakdown and eventual initial-level acceptance; we state an infinite run and eventual equality with the published trial-level recurrence. All curve restrictions refer only to their stated level intervals.
--
--   Differences from the source:
--   - encoding: Real n-dimensional vectors, continuously differentiable F, and the paper’s algorithm or local data. → Finite-dimensional real normed spaces (inner product spaces in §§7–8), fderiv with ContDiff ℝ 1, and explicit data predicates.; reason: These are coordinate-independent representations with exactly the stated norm; a run on infinite sequences means no breakdown.
--   - reading: Limit point, sufficiently near and sufficiently large; no breakdown. → MapClusterPt; one positive neighborhood radius for any local uniform hypothesis; eventual equality of trialLevel and the initial level; infinite run predicates.; reason: This is the paper’s explicit limit-point and breakdown convention on p. 396, with neighborhood and eventual quantifiers written out.
--   - correction: The parametrization following (8.1) writes a zero-damping inverse and η(0)=0 without treating singular derivatives or the undefined normalized residual when F(x)=0. → Use the closure of the positive-damping normal-equation branch; at singular zero damping its endpoint is the minimum-norm least-squares solution, and at zero residual the curve is zero. Equality is required only on the requested attainable subcurve.; reason: This completes the endpoint notation using (8.1) and continuity, preserving its regularization branch and both convergence conclusions and eventual acceptance for both algorithms. No global invertibility is added. The structured source audit records the singular example and the boundary domain.
-- source:
--   Eisenstat and Walker, Globally Convergent Inexact Newton Methods, SIAM J. Optim. 4(2) (1994), p. 419, Theorem 8.6; DOI 10.1137/0804022

import Mathlib
import Definitions.Def_GlobalInexactNewton_Backtracking_Method
import Definitions.Def_GlobalInexactNewton_Backtracking_Supplement_EqualityCurves
import Definitions.Def_GlobalInexactNewton_Backtracking_Supplement_LevenbergMarquardt

namespace GlobalInexactNewton.Backtracking.Supplement

open Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem theorem_8_6 (F : E → E) (hF : ContDiff ℝ 1 F)
    (ηmax t u θmin θmax : ℝ) (x : ℕ → E) (ηbar : ℕ → ℝ)
    (σ : ℕ → ℝ → E) (θ : ℕ → ℕ → ℝ) (m : ℕ → ℕ)
    (hrun : IsECMRRun F ηmax t θmin θmax x ηbar σ θ m ∨
      IsECTLRun F t u θmin θmax x ηbar σ θ m)
    (hcurve : ∀ k, IsLMCurve F (x k) (ηbar k) (σ k))
    (xstar : E) (hcluster : MapClusterPt xstar atTop x)
    (hinv : (fderiv ℝ F xstar).IsInvertible) :
    F xstar = 0 ∧ Tendsto x atTop (𝓝 xstar) ∧
      ∀ᶠ k in atTop, trialLevel (ηbar k) (θ k) (m k) = ηbar k := by sorry

end GlobalInexactNewton.Backtracking.Supplement
