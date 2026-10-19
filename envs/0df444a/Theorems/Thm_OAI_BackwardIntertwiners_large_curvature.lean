-- Prove2me | Theorems.Thm_OAI_BackwardIntertwiners_large_curvature
-- name    : OAI.BackwardIntertwiners.large_curvature
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:17:37.229568+00:00
-- url     : https://prove2.me/theorems/0fc60ceb-850e-4b6f-b21e-c3115b9c7089
-- title:
--   A sequence eventually above $\mu n^2$ has second differences exceeding $2\lambda$ infinitely often, for every $\lambda<\mu$
-- statement:
--   Let $F:\mathbb{N}\to\mathbb{R}$ be an arbitrary real sequence and let $\lambda,\mu\in\mathbb{R}$ with $\mu>0$ and $\lambda<\mu$. Suppose $F(n)\ge\mu n^2$ for all sufficiently large $n$. Then for every $N\in\mathbb{N}$ there exists $n\ge N$ with
--   $$F(n+2)-2F(n+1)+F(n)>2\lambda.$$
--   In other words, the second difference $\Delta^2F(n)=F(n+2)-2F(n+1)+F(n)$ exceeds $2\lambda$ for infinitely many $n$.
--
--   The second difference is the discrete analogue of $F''$: if $\Delta^2F\le2\lambda$ held from some point on, $F$ could grow at most like $\lambda n^2+O(n)$, which is incompatible with $F(n)\ge\mu n^2$. In the project this produces points of large curvature of quadratically growing convex profiles; at such points the contact property of convex envelopes makes coefficient bounds exact, which is what drives the correlation obstructions.
--
--   **Formalization Note** No convexity of $F$ is assumed, and $\lambda$ may be any real number below $\mu$ (for example $\lambda=0$, which yields infinitely many points with $\Delta^2F(n)>0$).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BackwardIntertwiners/ConvexEnvelope.lean#L244-L274

import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope

open OAI OAI.BackwardIntertwiners
open Filter
open scoped Topology

theorem OAI.BackwardIntertwiners.large_curvature {F : ℕ → ℝ} {lam μ : ℝ} (hμ : 0 < μ) (hlamμ : lam < μ)
    (hq : ∀ᶠ n : ℕ in atTop, μ * (n : ℝ)^2 ≤ F n) :
    ∀ N : ℕ, ∃ n, N ≤ n ∧ 2*lam < F (n+2) - 2*F (n+1) + F n := by sorry
