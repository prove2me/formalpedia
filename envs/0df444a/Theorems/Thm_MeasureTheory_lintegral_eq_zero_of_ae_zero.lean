-- Prove2me | Theorems.Thm_MeasureTheory_lintegral_eq_zero_of_ae_zero
-- name    : MeasureTheory.lintegral_eq_zero_of_ae_zero
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T18:02:43.327581+00:00
-- url     : https://prove2.me/theorems/c34ef05f-60b8-4f4b-a9e5-adff13c1c00f
-- title:
--   A lower integral vanishes when the integrand vanishes almost everywhere
-- statement:
--   **A non-negative integrand supported on a null set has zero lower integral.**
--
--   Let $f : \alpha \to [0,\infty]$ and let $s$ be a measurable set whose complement is null,
--   $\mu(s^{c}) = 0$. If $f$ vanishes on $s$, then
--
--   $$\int^{-} f \,d\mu \;=\; 0 .$$
--
--   Splitting the integral over $s$ and $s^{c}$, the contribution from $s$ is $0$ because $f$
--   vanishes there, and the contribution from $s^{c}$ is $0$ because the set is null — even though
--   $f$ may be arbitrary, indeed $+\infty$, on $s^{c}$. This last point is what makes the statement
--   worth having: it is a genuine "almost everywhere" result, requiring no control on $f$ off $s$.
--
--   Lower (`lintegral`) integration of $[0,\infty]$-valued functions is where Mathlib's measure
--   theory does its work before passing to Bochner integrals, and this lemma is the standard way to
--   discard a null set — for instance when an identity between two functions is known only almost
--   everywhere and one wants to conclude equality of their integrals.
--
--   **Formalization note.** `∫⁻` is the lower Lebesgue integral for `ℝ≥0∞`-valued functions, where
--   no integrability hypothesis is needed since the value $+\infty$ is permitted.
-- source:
--   Standard measure theory; adapted from material vendored in `Salt/Entropy/` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey), itself derived from the Polynomial Freiman–Ruzsa project (Terence Tao and contributors, Apache-2.0).

import Mathlib

namespace MeasureTheory

open MeasureTheory ENNReal in
theorem lintegral_eq_zero_of_ae_zero {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} {f : α → ℝ≥0∞} (hs : μ sᶜ = 0) (hf : ∀ x ∈ s, f x = 0)
    (hmes : MeasurableSet s) :
    ∫⁻ x, f x ∂μ = 0 := by sorry

end MeasureTheory
