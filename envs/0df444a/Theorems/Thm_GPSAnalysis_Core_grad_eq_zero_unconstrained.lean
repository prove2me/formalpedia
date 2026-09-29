-- Prove2me | Theorems.Thm_GPSAnalysis_Core_grad_eq_zero_unconstrained
-- name    : GPSAnalysis.Core.grad_eq_zero_unconstrained
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T07:57:58.071223+00:00
-- url     : https://prove2.me/theorems/a6bd8bb1-c7ee-4ddb-9089-60aa1fb8c86a
-- title:
--   Theorem 3.9 — unconstrained case: $\nabla f(\hat x)=0$ at strictly differentiable limits
-- statement:
--   Consider a GPS run satisfying A1 ($f_\Omega(x_0)<\infty$) and A3 (all iterates lie in a compact set), with $\Omega=\mathbb R^n$. Let $\hat x$ be the limit of a refining subsequence, and assume, as throughout Section 3.4 of the paper, that $f$ is Lipschitz near $\hat x$. If $f$ is strictly differentiable at $\hat x$, with strict gradient $\nabla f(\hat x)$, then
--
--   $$\nabla f(\hat x)=0 .$$
--
--   This is the strongest stationarity statement the paper expects in the unconstrained case, and it applies to functions that are strictly differentiable at the limit point without being continuously differentiable near it.
--
--   **Formalization Note** $f=g$ on a neighbourhood $U$ of $\hat x$ with $g$ real-valued and Lipschitz on $U$; strict differentiability is the directional notion of Section 3.4: $\frac{g(y+tw)-g(y)}{t}\to\nabla f(\hat x)^T w$ as $y\to\hat x$, $t\downarrow 0$, for every $w$.
-- source:
--   Audet, Dennis, Analysis of Generalized Pattern Searches, SIAM J. Optim. 13 (2003), p. 898, Section 3.4 and Theorem 3.9

import Mathlib
import Definitions.Def_GPSAnalysis_Core_Problem
import Definitions.Def_GPSAnalysis_Core_Mesh
import Definitions.Def_GPSAnalysis_Core_Run
import Definitions.Def_GPSAnalysis_Core_Clarke

open Filter Topology

namespace GPSAnalysis.Core

/-- Theorem 3.9 (Audet–Dennis 2003, p. 898). Under A1 and A3, let `Ω = ℝⁿ` and let `x̂` be the
limit of a refining subsequence. If `f` is Lipschitz near `x̂` (`f = g` on a neighbourhood
`U`, `g` Lipschitz on `U`) and strictly differentiable at `x̂` with strict gradient `∇f(x̂)`,
then `∇f(x̂) = 0`. -/
theorem grad_eq_zero_unconstrained {n m p : ℕ} (P : GPSSetup n m p) (R : GPSRun P)
    (hΩ : P.Ω = Set.univ) (hA1 : AssumptionA1 R) (hA3 : AssumptionA3 R)
    (K : ℕ → ℕ) (hK : IsRefiningSubseq R K) (xhat : Fin n → ℝ)
    (hlim : Tendsto (fun i => R.x (K i)) atTop (𝓝 xhat))
    (U : Set (Fin n → ℝ)) (hU : U ∈ 𝓝 xhat) (g : (Fin n → ℝ) → ℝ)
    (hfg : ∀ y ∈ U, P.f y = (g y : WithTop ℝ)) (L : NNReal) (hL : LipschitzOnWith L g U)
    (grad : Fin n → ℝ) (hgrad : HasStrictDirGradAt g grad xhat) :
    grad = 0 := by sorry

end GPSAnalysis.Core
