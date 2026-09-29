-- Prove2me | Theorems.Thm_NonsmoothNewton_Local_prop_3_1
-- name    : NonsmoothNewton.Local.prop_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T00:03:37.315187+00:00
-- url     : https://prove2.me/theorems/a2f39e9f-7289-48b1-b7e6-3c890db1f5c1
-- title:
--   Proposition 3.1 — uniform bound on $\|V^{-1}\|$ near a point where $\partial F$ is nonsingular
-- statement:
--   Let $F : \mathbb R^n \to \mathbb R^n$ be locally Lipschitz and $x \in \mathbb R^n$. If every $V \in \partial F(x)$ is nonsingular, then there are a neighbourhood $N(x)$ of $x$ and a constant $C$ such that for every $y \in N(x)$ and every $V \in \partial F(y)$, $V$ is nonsingular and
--
--   $$
--   \|V^{-1}\| \le C .
--   $$
--
--   This is the uniform invertibility that makes every Newton step near a regular root well defined and controls its size.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` with the Euclidean norm, and $\|V^{-1}\|$ is the corresponding operator norm; "nonsingular with inverse of norm at most $C$" is written as the existence of a two-sided inverse $W$ with $\|W\| \le C$. Section 3's standing assumption "$F$ locally Lipschitzian" is a hypothesis, although the proposition's sentence does not repeat it.
-- source:
--   Qi, Sun, A nonsmooth version of Newton's method, Math. Programming 58 (1993), p. 359, Proposition 3.1 (standing assumption p. 358)

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
open Filter Topology

namespace NonsmoothNewton.Local

/-- Qi–Sun (1993), Proposition 3.1, p. 359 (Section 3 standing assumption: `F : ℝⁿ → ℝⁿ`
locally Lipschitz). If every `V ∈ ∂F(x)` is nonsingular, there are a neighbourhood `N(x)`
and a constant `C` such that every `V ∈ ∂F(y)`, `y ∈ N(x)`, is nonsingular with
`‖V⁻¹‖ ≤ C`. -/
theorem prop_3_1 {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hF : LocallyLipschitz F)
    (x : EuclideanSpace ℝ (Fin n)) (hns : ∀ V ∈ NonsmoothNewton.Shared.clarkeJac F x, IsUnit V) :
    ∃ N ∈ 𝓝 x, ∃ C : ℝ, ∀ y ∈ N, ∀ V ∈ NonsmoothNewton.Shared.clarkeJac F y,
      ∃ W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
        V.comp W = ContinuousLinearMap.id ℝ _ ∧ W.comp V = ContinuousLinearMap.id ℝ _ ∧
        ‖W‖ ≤ C := by sorry

end NonsmoothNewton.Local
