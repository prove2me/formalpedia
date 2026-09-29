-- Prove2me | Theorems.Thm_MeasureTheory_lintegral_eq_single
-- name    : MeasureTheory.lintegral_eq_single
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T18:06:52.36744+00:00
-- url     : https://prove2.me/theorems/dcd238ab-85fa-4fd4-bc52-92c64e00e38b
-- title:
--   A lower integral concentrated at a point
-- statement:
--   **An integrand supported at a single point integrates to its value times the point mass.**
--
--   Let $f : \alpha \to [0,\infty]$ vanish outside a single point $a$. Then
--
--   $$\int^{-} f \,d\mu \;=\; f(a)\,\mu(\{a\}).$$
--
--   Splitting the integral at $\{a\}$, the contribution from the complement vanishes because $f$
--   does, and over $\{a\}$ the integrand is the constant $f(a)$, giving $f(a)\mu(\{a\})$. The
--   `MeasurableSingletonClass` hypothesis is what makes $\{a\}$ measurable so the split is
--   legitimate.
--
--   This is the bridge between integration and summation for atomic measures. For a counting or
--   discrete measure, a general integrand decomposes as a sum of such single-point pieces, and this
--   lemma evaluates each one; that is how $\int f\,d\mu$ becomes $\sum_x f(x)\mu(\{x\})$ — the
--   identity underlying every computation of a discrete expectation or a Shannon entropy as a sum.
--
--   **Formalization note.** `∫⁻` is the lower Lebesgue integral for $[0,\infty]$-valued functions,
--   so no integrability hypothesis is needed; the product on the right is taken in `ENNReal`, where
--   $\infty \cdot 0 = 0$ handles the degenerate cases.
-- source:
--   Standard measure theory; adapted from material vendored in `Salt/Entropy/` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey), itself derived from the Polynomial Freiman–Ruzsa project (Terence Tao and contributors, Apache-2.0).

import Mathlib

namespace MeasureTheory

open MeasureTheory ENNReal in
theorem lintegral_eq_single {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) (a : α) (f : α → ℝ≥0∞) (ha : ∀ b ≠ a, f b = 0) :
    ∫⁻ x, f x ∂μ = f a * μ {a} := by sorry

end MeasureTheory
