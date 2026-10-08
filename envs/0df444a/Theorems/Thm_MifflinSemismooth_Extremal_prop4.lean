-- Prove2me | Theorems.Thm_MifflinSemismooth_Extremal_prop4
-- name    : MifflinSemismooth.Extremal.prop4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:34:25.936045+00:00
-- url     : https://prove2.me/theorems/4f1742d9-bbd3-471d-a906-63e64e07a94a
-- title:
--   Proposition 4, p. 6 — a C¹ function is locally Lipschitz, ∂F(x) = {∇F(x)}, quasidifferentiable and semismooth
-- statement:
--   Let $F:\mathbb R^n\to\mathbb R$ be continuously differentiable. Then
--
--   1. $F$ is locally Lipschitz (Lipschitz on each bounded subset of $\mathbb R^n$);
--   2. $\partial F(x)=\{\nabla F(x)\}$ for each $x\in\mathbb R^n$;
--   3. $F$ is quasidifferentiable on $\mathbb R^n$;
--   4. $F$ is semismooth on $\mathbb R^n$.
--
--   Continuously differentiable functions are the second family of basic examples; Theorem 2 extends semismoothness from them to their pointwise maxima and minima over compact families.
--
--   **Formalization Note.** "Continuously differentiable" is `ContDiff ℝ 1 F`; $\nabla F$ is Mathlib's `gradient F`.
-- source:
--   Mifflin, Semismooth and semiconvex functions in constrained optimization, IIASA Research Report RR-76-21 (December 1976), p. 6, §2, Proposition 4

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_genDirDeriv
import Definitions.Def_ClarkeGradients_Shared_LipschitzOnBounded
import Definitions.Def_MifflinSemismooth_Extremal_Basic

open Filter Topology

namespace MifflinSemismooth.Extremal

/-- Mifflin (1976), Proposition 4, p. 6: a continuously differentiable `F : ℝⁿ → ℝ` is locally
Lipschitz, `∂F(x) = {∇F(x)}` for each `x`, and `F` is quasidifferentiable and semismooth on `ℝⁿ`. -/
theorem prop4 {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ContDiff ℝ 1 F) :
    ClarkeGradients.Shared.LipschitzOnBounded F ∧
    (∀ x, genGrad F x = {gradient F x}) ∧
    QuasidiffOn F Set.univ ∧ SemismoothOn F Set.univ := by sorry

end MifflinSemismooth.Extremal
