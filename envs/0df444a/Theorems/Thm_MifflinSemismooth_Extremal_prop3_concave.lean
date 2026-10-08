-- Prove2me | Theorems.Thm_MifflinSemismooth_Extremal_prop3_concave
-- name    : MifflinSemismooth.Extremal.prop3_concave
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:34:15.778457+00:00
-- url     : https://prove2.me/theorems/cf14a1b0-ec95-40a9-8675-92545acb4144
-- title:
--   Proposition 3, p. 5, concave case — concave F is locally Lipschitz, ∂F is the superdifferential, −F is semiconvex, F is semismooth
-- statement:
--   Let $F:\mathbb R^n\to\mathbb R$ be concave. Then
--
--   1. $F$ is locally Lipschitz (Lipschitz on each bounded subset of $\mathbb R^n$);
--   2. for each $x\in\mathbb R^n$, $$\partial F(x)=\{g\in\mathbb R^n:\ F(y)\le F(x)+\langle g,y-x\rangle\ \text{for all } y\in\mathbb R^n\};$$
--   3. $-F$ is semiconvex on $\mathbb R^n$ (with respect to $\mathbb R^n$);
--   4. $F$ is semismooth on $\mathbb R^n$.
--
--   This is the concave half of Proposition 3; concave functions are semismooth as well.
--
--   **Formalization Note.** The page's parentheticals "$F(F)$ is locally Lipschitz", "$\ge(\le)$", "$F(-F)$ is semiconvex" and "$F(F)$ is semismooth" are read as "respectively", giving the four claims above.
-- source:
--   Mifflin, Semismooth and semiconvex functions in constrained optimization, IIASA Research Report RR-76-21 (December 1976), p. 5, §2, Proposition 3 (concave case)

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_genDirDeriv
import Definitions.Def_ClarkeGradients_Shared_LipschitzOnBounded
import Definitions.Def_MifflinSemismooth_Extremal_Basic

open Filter Topology

namespace MifflinSemismooth.Extremal

/-- Mifflin (1976), Proposition 3, p. 5, concave case: a concave `F : ℝⁿ → ℝ` is locally
Lipschitz, `∂F(x) = {g : F(y) ≤ F(x) + ⟨g, y - x⟩ for all y}` at each `x`, `-F` is semiconvex on
`ℝⁿ`, and `F` is semismooth on `ℝⁿ`. -/
theorem prop3_concave {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ConcaveOn ℝ Set.univ F) :
    ClarkeGradients.Shared.LipschitzOnBounded F ∧
    (∀ x, genGrad F x = {g | ∀ y, F y ≤ F x + inner ℝ g (y - x)}) ∧
    SemiconvexOn Set.univ (fun y => -F y) ∧ SemismoothOn F Set.univ := by sorry

end MifflinSemismooth.Extremal
