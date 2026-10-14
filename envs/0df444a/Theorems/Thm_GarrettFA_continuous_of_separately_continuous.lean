-- Prove2me | Theorems.Thm_GarrettFA_continuous_of_separately_continuous
-- name    : GarrettFA.continuous_of_separately_continuous
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T19:31:41.616415+00:00
-- url     : https://prove2.me/theorems/69075e47-1d5f-4fe2-b5d8-b9b2c304d689
-- title:
--   Cor. 3.0.3 — separately continuous bilinear maps on Fréchet spaces are continuous
-- statement:
--   Let $X, Y, Z$ be Fréchet spaces over $\mathbb K=\mathbb R$ or $\mathbb C$ and let $\beta: X\times Y\to Z$ be a bilinear map that is continuous in each variable separately. Then
--
--   $$\beta : X\times Y\to Z \ \text{ is jointly continuous.}$$
--
--   **Formalization Note** $\beta$ is a $\mathbb K$-bilinear map, given as a linear map $X\to(Y\to_{\mathbb K} Z)$.
-- source:
--   Paul Garrett, *Completeness and quasi-completeness* (lecture notes, April 24, 2014), http://www.math.umn.edu/~garrett/m/fun/notes_2012-13/07d_quasi-completeness.pdf, p. 5, Corollary 3.0.3

import Definitions.Def_GarrettFA_IsFrechetSpace

namespace GarrettFA
theorem continuous_of_separately_continuous {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [AddCommGroup X] [Module 𝕜 X] [Module ℝ X]
    [IsScalarTower ℝ 𝕜 X] [UniformSpace X] [IsUniformAddGroup X] [ContinuousSMul 𝕜 X] [T2Space X]
    {Y : Type*} [AddCommGroup Y] [Module 𝕜 Y] [Module ℝ Y]
    [IsScalarTower ℝ 𝕜 Y] [UniformSpace Y] [IsUniformAddGroup Y] [ContinuousSMul 𝕜 Y] [T2Space Y]
    {Z : Type*} [AddCommGroup Z] [Module 𝕜 Z] [Module ℝ Z]
    [IsScalarTower ℝ 𝕜 Z] [UniformSpace Z] [IsUniformAddGroup Z] [ContinuousSMul 𝕜 Z] [T2Space Z]
    (hX : IsFrechetSpace 𝕜 X) (hY : IsFrechetSpace 𝕜 Y) (hZ : IsFrechetSpace 𝕜 Z)
    (β : X →ₗ[𝕜] Y →ₗ[𝕜] Z) (h₁ : ∀ x : X, Continuous (β x))
    (h₂ : ∀ y : Y, Continuous (fun x : X => β x y)) :
    Continuous (fun p : X × Y => β p.1 p.2) := by sorry
end GarrettFA
