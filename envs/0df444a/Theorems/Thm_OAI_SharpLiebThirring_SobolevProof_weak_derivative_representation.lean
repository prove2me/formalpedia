-- Prove2me | Theorems.Thm_OAI_SharpLiebThirring_SobolevProof_weak_derivative_representation
-- name    : OAI.SharpLiebThirring.SobolevProof.weak_derivative_representation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T13:57:20.786644+00:00
-- url     : https://prove2.me/theorems/fb8df070-d1bb-42ce-ba4e-fefdb7df6fb0
-- title:
--   A function on the line with a locally integrable weak derivative is a.e. the primitive of that derivative
-- statement:
--   **Statement.** Let $f, g : \mathbb R \to \mathbb R$ be locally integrable, and let $g$ be the weak derivative of $f$:
--   $$\int_{\mathbb R} f(x)\,\varphi'(x)\,dx = -\int_{\mathbb R} g(x)\,\varphi(x)\,dx$$
--   for every smooth compactly supported $\varphi : \mathbb R \to \mathbb R$. Then there is a constant $c$ with
--   $$f(x) = c + \int_0^x g(t)\,dt \quad\text{for almost every } x.$$
--
--   So every function in $W^{1,1}_{\mathrm{loc}}(\mathbb R)$ has an absolutely continuous representative, the primitive of its weak derivative. This is the classical one-dimensional Sobolev representation, and it follows from the du Bois-Reymond lemma, published here as `OAI.SharpLiebThirring.SobolevProof.ae_const_of_weak_derivative_zero`. The statement uses only Mathlib. Lean: `OAI.SharpLiebThirring.SobolevProof.weak_derivative_representation`, OpenAI's lemma of that name (in `lean/OAI/Analysis/LiebThirring/SobolevProjection.lean`).
-- source:
--   OpenAI, Sharp one-dimensional Lieb–Thirring constants, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 262; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-One-Dimensional-Lieb-Thirring-Constants-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LiebThirring/SobolevProjection.lean (declaration OAI.SharpLiebThirring.SobolevProof.weak_derivative_representation)

import Mathlib

open MeasureTheory
open scoped ContDiff

theorem OAI.SharpLiebThirring.SobolevProof.weak_derivative_representation
    {f g : ℝ → ℝ}
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume)
    (hw : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, f x * deriv φ x) = -(∫ x, g x * φ x)) :
    ∃ c : ℝ, f =ᵐ[volume] fun x ↦ c + ∫ t in (0 : ℝ)..x, g t := by
  sorry
