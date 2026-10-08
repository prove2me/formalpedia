-- Prove2me | Theorems.Thm_MifflinSemismooth_Extremal_prop3_convex
-- name    : MifflinSemismooth.Extremal.prop3_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:36:20.654419+00:00
-- url     : https://prove2.me/theorems/64cc248a-b7e2-42f9-85d8-f9585b75b513
-- title:
--   Proposition 3, p. 5, convex case — convex F is locally Lipschitz, ∂F is the subdifferential, F is semiconvex and semismooth
-- statement:
--   Let $F:\mathbb R^n\to\mathbb R$ be convex. Then
--
--   1. $F$ is locally Lipschitz (Lipschitz on each bounded subset of $\mathbb R^n$);
--   2. for each $x\in\mathbb R^n$, $$\partial F(x)=\{g\in\mathbb R^n:\ F(y)\ge F(x)+\langle g,y-x\rangle\ \text{for all } y\in\mathbb R^n\},$$ i.e. $\partial F$ is the subdifferential of convex analysis;
--   3. $F$ is semiconvex on $\mathbb R^n$ (with respect to $\mathbb R^n$);
--   4. $F$ is semismooth on $\mathbb R^n$.
--
--   Convex functions are the first family of examples of semismooth and semiconvex functions.
--
--   **Formalization Note.** "Locally Lipschitz" is the published `ClarkeGradients.Shared.LipschitzOnBounded`. The page states the convex and concave cases in one sentence with parentheses; this item is the convex case and `prop3_concave` the concave case.
-- source:
--   Mifflin, Semismooth and semiconvex functions in constrained optimization, IIASA Research Report RR-76-21 (December 1976), p. 5, §2, Proposition 3 (convex case)

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_genDirDeriv
import Definitions.Def_ClarkeGradients_Shared_LipschitzOnBounded
import Definitions.Def_MifflinSemismooth_Extremal_Basic

open Filter Topology

namespace MifflinSemismooth.Extremal

/-- Mifflin (1976), Proposition 3, p. 5, convex case: a convex `F : ℝⁿ → ℝ` is locally Lipschitz,
`∂F(x)` is the subdifferential of `F` at each `x`, and `F` is semiconvex and semismooth on `ℝⁿ`. -/
theorem prop3_convex {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ConvexOn ℝ Set.univ F) :
    ClarkeGradients.Shared.LipschitzOnBounded F ∧
    (∀ x, genGrad F x = {g | ∀ y, F x + inner ℝ g (y - x) ≤ F y}) ∧
    SemiconvexOn Set.univ F ∧ SemismoothOn F Set.univ := by sorry

end MifflinSemismooth.Extremal
