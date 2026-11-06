-- Prove2me | Theorems.Thm_GlobalSinkhorn_scalingRadius_attained
-- name    : GlobalSinkhorn.scalingRadius_attained
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T04:22:26.991197+00:00
-- url     : https://prove2.me/theorems/d5844f8c-9cb2-47a9-a77b-85dc004f81b4
-- title:
--   Definition 2.1 — the minimum defining $D(A;B)$ is attained
-- statement:
--   Let $n\ge1$, let $A\in\mathbb R^{n\times n}_{\ge0}$ be row-stochastic, and let $B$ be a doubly stochastic matrix that is a positive diagonal scaling of $A$. Then the minimum in the definition of the logarithmic scaling radius is attained: there are $u,v\in\mathbb R^n$ with
--   $$
--   B=\operatorname{diag}(e^{u})\,A\,\operatorname{diag}(e^{-v})\qquad\text{and}\qquad \max\{\|u\|_\infty,\|v\|_\infty\}=D(A;B).
--   $$
--   This justifies writing $D(A;B)$ as a minimum and supplies the minimizing pair used in the proof of Theorem 1.1.
--
--   Differences from the source:
--   - encoding: indices [n] = {1,…,n} → Fin n (0-based); reason: Lean convention; same instances
--   - encoding: n a positive integer (p.13: n ∈ ℤ_{>0}) → hypothesis 0 < n; reason: the paper's standing convention made explicit
--   - encoding: "the minimum is attained" for D(A;B) = min{…} → ∃ feasible (u, v) with max ‖u‖ ‖v‖ = scalingRadius A B, where scalingRadius is an sInf; reason: the claim is exactly that the infimum of the feasible values is one of them
--   - encoding: B doubly stochastic positive diagonal scaling of A → B ∈ doublyStochastic ℝ (Fin n) ∧ ∃ x y, IsPosDiagScaling A B x y; reason: the hypotheses of Definition 2.1 written out
-- source:
--   He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef1311fa669023fddd0c074df8a61571bf17b5712615c09d1495a34034ad), Definition 2.1, p.13

import Mathlib
import Definitions.Def_GlobalSinkhorn_IsPosDiagScaling
import Definitions.Def_GlobalSinkhorn_scalingRadius

open Matrix

namespace GlobalSinkhorn

/-- The minimum in Definition 2.1 is attained. He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef13…34ad), Definition 2.1, p.13. -/
theorem scalingRadius_attained {n : ℕ} (hn : 0 < n) (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.rowStochastic ℝ (Fin n))
    (hB : B ∈ doublyStochastic ℝ (Fin n))
    (hAB : ∃ x y : Fin n → ℝ, IsPosDiagScaling A B x y) :
    ∃ u v : Fin n → ℝ,
      B = Matrix.diagonal (fun i => Real.exp (u i)) * A *
          Matrix.diagonal (fun j => Real.exp (-v j)) ∧
        max ‖u‖ ‖v‖ = scalingRadius A B := by sorry

end GlobalSinkhorn
