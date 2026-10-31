-- Prove2me | Theorems.Thm_MaskedLinx_display_19_b_pos
-- name    : MaskedLinx.display_19_b_pos
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:39:20.522978+00:00
-- url     : https://prove2.me/theorems/6a9e535c-3c30-4f2e-bb23-a409cfda06cb
-- title:
--   Display (19) — $b_{c_1,c_2}=\min_{\gamma>0}\sum_{i=1}^2\log\big(\tfrac{(1-c_i^2)^2}{4}\gamma+\tfrac{1+c_i^2}{2}+\tfrac1{4\gamma}\big)>0$
-- statement:
--   Let $c_1,c_2$ be real numbers with $c_1^2\le1$, $c_2^2\le1$ and $c_1^2\ne c_2^2$. For $\gamma>0$ put
--
--   $$\varphi(\gamma)=\sum_{i=1}^{2}\log\Big(\frac{(1-c_i^2)^2}{4}\,\gamma+\frac{1+c_i^2}{2}+\frac1{4\gamma}\Big).$$
--
--   Then the minimum of $\varphi$ over $\gamma>0$ is attained, and its value
--
--   $$b_{c_1,c_2}:=\min_{\gamma>0}\varphi(\gamma)$$
--
--   is strictly positive. Concretely: there is $\gamma_0>0$ with $\varphi(\gamma_0)\le\varphi(\gamma)$ for all $\gamma>0$, and $\varphi(\gamma_0)>0$.
--
--   In the proof of Theorem 4.1, $c_1$ and $c_2$ are the off-diagonal entries of the two kinds of $2\times2$ blocks of the witness matrices, and $b_{c_1,c_2}/8$ is the slope of the linear gap.
--
--   **Formalization Note** For $\gamma>0$ every argument of the logarithm is positive, so no junk value of `Real.log` occurs.
--
--   Differences from the source:
--   - encoding: b_{c₁,c₂} := min_{γ>0} … > 0 → there is γ₀ > 0 minimizing φ over γ > 0, and φ(γ₀) > 0; reason: the paper's min asserts attainment; the explicit minimizer avoids an ℝ-valued infimum with junk values
-- source:
--   Chen, Fampa, Lee, Masking Anstreicher's linx bound for improved entropy bounds, arXiv:2106.02980v1, §4, proof of Theorem 4.1, display (19), p.13 (the hypotheses c₁² ≤ 1, c₂² ≤ 1 and c₁² ≠ c₂² from the same proof)

import Mathlib

namespace MaskedLinx

/-- **Display (19): `b_{c₁,c₂} > 0`.**
Chen, Fampa, Lee, *Masking Anstreicher's linx bound for improved entropy bounds*,
arXiv:2106.02980v1, §4, proof of Theorem 4.1, display (19), p.13:
"Thus we can choose c₁² ≠ c₂², then for all possible values of c₁,c₂,
b_{c₁,c₂} := min_{γ>0} Σ_{i=1}^{2} log(((1−cᵢ²)²/4)γ + (1+cᵢ²)/2 + 1/(4γ)) > 0."
The surrounding text fixes `c₁² ≤ 1`, `c₂² ≤ 1`.

The statement asserts both that the minimum over `γ > 0` is attained (at some `γ₀ > 0`) and
that its value is positive.

**Formalization Note.** For `γ > 0` every argument of `Real.log` is positive, so no junk value
of the logarithm is involved. -/
theorem display_19_b_pos (c₁ c₂ : ℝ) (h₁ : c₁ ^ 2 ≤ 1) (h₂ : c₂ ^ 2 ≤ 1)
    (hne : c₁ ^ 2 ≠ c₂ ^ 2) :
    let φ : ℝ → ℝ := fun γ =>
      Real.log ((1 - c₁ ^ 2) ^ 2 / 4 * γ + (1 + c₁ ^ 2) / 2 + 1 / (4 * γ)) +
      Real.log ((1 - c₂ ^ 2) ^ 2 / 4 * γ + (1 + c₂ ^ 2) / 2 + 1 / (4 * γ))
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ (∀ γ : ℝ, 0 < γ → φ γ₀ ≤ φ γ) ∧ 0 < φ γ₀ := by sorry

end MaskedLinx
