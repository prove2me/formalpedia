-- Prove2me | Theorems.Thm_OAI_SharpLiebThirring_SobolevProof_ae_const_of_weak_derivative_zero
-- name    : OAI.SharpLiebThirring.SobolevProof.ae_const_of_weak_derivative_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T13:57:20.385756+00:00
-- url     : https://prove2.me/theorems/ec06fef8-84fb-4748-8b1b-9f4045a2a46d
-- title:
--   Du Bois-Reymond lemma: a locally integrable function with zero weak derivative is constant
-- statement:
--   **Statement.** Let $f : \mathbb R \to \mathbb R$ be locally integrable for Lebesgue measure. Suppose
--   $$\int_{\mathbb R} f(x)\,\varphi'(x)\,dx = 0$$
--   for every smooth compactly supported $\varphi : \mathbb R \to \mathbb R$, so that the distributional derivative of $f$ vanishes. Then $f$ is almost everywhere equal to a constant: there is $c \in \mathbb R$ with $f = c$ a.e.
--
--   This is the du Bois-Reymond lemma in its distributional form: a distribution on the line with zero derivative is a constant. Only smooth compactly supported test functions are used, so it applies to weak derivatives in the sense of $H^1$ and $W^{1,1}_{\mathrm{loc}}$. The statement uses only Mathlib. Lean: `OAI.SharpLiebThirring.SobolevProof.ae_const_of_weak_derivative_zero`, OpenAI's lemma of that name (in `lean/OAI/Analysis/LiebThirring/SobolevProjection.lean`).
-- source:
--   OpenAI, Sharp one-dimensional Lieb–Thirring constants, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 262; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-One-Dimensional-Lieb-Thirring-Constants-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LiebThirring/SobolevProjection.lean (declaration OAI.SharpLiebThirring.SobolevProof.ae_const_of_weak_derivative_zero)

import Mathlib

open MeasureTheory
open scoped ContDiff

theorem OAI.SharpLiebThirring.SobolevProof.ae_const_of_weak_derivative_zero
    {f : ℝ → ℝ} (hf : LocallyIntegrable f volume)
    (hw : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, f x * deriv φ x) = 0) : ∃ c : ℝ, f =ᵐ[volume] fun _ ↦ c := by
  sorry
