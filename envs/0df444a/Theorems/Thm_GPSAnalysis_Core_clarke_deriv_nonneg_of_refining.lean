-- Prove2me | Theorems.Thm_GPSAnalysis_Core_clarke_deriv_nonneg_of_refining
-- name    : GPSAnalysis.Core.clarke_deriv_nonneg_of_refining
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T07:53:53.210953+00:00
-- url     : https://prove2.me/theorems/3b72b0c3-cf51-4b09-b79c-c86182398fc5
-- title:
--   Theorem 3.7 — nonnegative Clarke derivatives at limits of refining subsequences
-- statement:
--   Consider a GPS run on problem (1.1) satisfying A1 ($f_\Omega(x_0)<\infty$), A2 ($A$ rational) and A3 (all iterates lie in a compact set). Let $\{x_k\}_{k\in K}$ be a refining subsequence converging to $\hat x$, and let $d\in D$ be a direction for which $f$ was evaluated at a poll step for infinitely many iterates of the subsequence: $d\in D_k$ and the poll point $x_k+\Delta_k d$ is feasible for infinitely many $k\in K$. If $f$ is Lipschitz near $\hat x$, then
--
--   $$f^\circ(\hat x;d)\ \ge\ 0,$$
--
--   where $f^\circ(\hat x;d)=\limsup_{y\to\hat x,\,t\downarrow 0}\frac{f(y+td)-f(y)}{t}$ is Clarke's generalized directional derivative.
--
--   This is the main result of the paper. It holds for extended-valued, discontinuous objectives (only local Lipschitz continuity at the limit point is assumed) and yields the unconstrained and linearly constrained optimality results as corollaries.
--
--   **Formalization Note** "$f$ is Lipschitz near $\hat x$" is expressed as: $f=g$ on a neighbourhood $U$ of $\hat x$ for a real-valued $g$ that is Lipschitz on $U$; the conclusion is stated for every such $g$, and $f^\circ(\hat x;d)$ is $g$'s Clarke derivative, which depends only on values near $\hat x$. Under the barrier, $f$ is evaluated exactly at the feasible trial points, hence the feasibility requirement on the poll points.
-- source:
--   Audet, Dennis, Analysis of Generalized Pattern Searches, SIAM J. Optim. 13 (2003), p. 897, Theorem 3.7 and Eq. (3.1)

import Mathlib
import Definitions.Def_GPSAnalysis_Core_Problem
import Definitions.Def_GPSAnalysis_Core_Mesh
import Definitions.Def_GPSAnalysis_Core_Run
import Definitions.Def_GPSAnalysis_Core_Clarke

open Filter Topology

namespace GPSAnalysis.Core

/-- Theorem 3.7 (Audet–Dennis 2003, p. 897), the main result. Under A1–A3, let `x̂` be the limit
of a refining subsequence `{x_k}_{k ∈ K}`, let `d = d_j` be a direction of `D` such that, for
infinitely many iterates of the subsequence, `d ∈ D_k` and the poll point `x_k + Δ_k d` is
feasible (so `f` was evaluated there), and let `f` be Lipschitz near `x̂`: `f = g` on a
neighbourhood `U` of `x̂` for a real function `g` Lipschitz on `U`. Then `f°(x̂; d) ≥ 0`. -/
theorem clarke_deriv_nonneg_of_refining {n m p : ℕ} (P : GPSSetup n m p) (R : GPSRun P)
    (hA1 : AssumptionA1 R) (hA2 : AssumptionA2 P) (hA3 : AssumptionA3 R)
    (K : ℕ → ℕ) (hK : IsRefiningSubseq R K) (xhat : Fin n → ℝ)
    (hlim : Tendsto (fun i => R.x (K i)) atTop (𝓝 xhat))
    (j : Fin p)
    (hj : ∃ᶠ i in atTop, j ∈ R.Dk (K i) ∧ R.x (K i) + R.Δ (K i) • P.dir j ∈ P.Ω)
    (U : Set (Fin n → ℝ)) (hU : U ∈ 𝓝 xhat) (g : (Fin n → ℝ) → ℝ)
    (hfg : ∀ y ∈ U, P.f y = (g y : WithTop ℝ)) (L : NNReal) (hL : LipschitzOnWith L g U) :
    0 ≤ clarkeDirDeriv g xhat (P.dir j) := by sorry

end GPSAnalysis.Core
