-- Prove2me | Theorems.Thm_HedgeInv_Order_lemma2_i
-- name    : HedgeInv.Order.lemma2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:22:02.170979+00:00
-- url     : https://prove2.me/theorems/6117a4f9-99aa-414a-8274-9713138d3459
-- title:
--   Lemma 2(i), p. 118 (weak form) — f decreasing with E[f(X)] = 0 and w decreasing, nonnegative ⇒ E[w(X)f(X)] ≥ 0
-- statement:
--   Let $X$ be a real random variable with law $\mu$. Let $f:\mathbb R\to\mathbb R$ be nonincreasing with $f(X)$ integrable and $E[f(X)]=0$. Let $w:\mathbb R\to\mathbb R$ be nonincreasing and nonnegative, with $w(X)f(X)$ integrable. Then
--   $$E[w(X)\,f(X)]\ \ge\ 0.$$
--
--   This is a one-variable Chebyshev (association) inequality: two functions that move in the same direction are nonnegatively correlated. In the paper it gives the sign of the first term in the cross-partial derivative (25), and, extended to an $f$ with nonnegative mean, the monotonicity of $E_\varepsilon[u''(\Pi)\mid S_T]$.
--
--   **Formalization Note.** The paper prints a strict inequality $E[w(X)f(X)]>0$, which fails for $w\equiv1$ (the left side is then $E[f(X)]=0$). The weak inequality is stated here, and it is the form the proof of Proposition 7 uses. "Decreasing" is read as nonincreasing.
-- source:
--   Gaur & Seshadri, Hedging Inventory Risk Through Market Instruments, Manuf. Serv. Oper. Manag. 7(2) (2005), p. 118, Lemma 2(i)

import Mathlib

namespace HedgeInv.Order

open MeasureTheory

/-- Lemma 2(i), p. 118, in the weak form: if `f` is nonincreasing with `E[f(X)] = 0` and `w` is
nonincreasing and nonnegative, then `E[w(X) f(X)] ≥ 0`. `μ` is the law of `X`. (The printed
strict inequality fails for `w ≡ 1`.) -/
theorem lemma2_i (μ : Measure ℝ) [IsProbabilityMeasure μ] (f w : ℝ → ℝ)
    (hf : Antitone f) (hw : Antitone w) (hw0 : ∀ x, 0 ≤ w x)
    (hfi : Integrable f μ) (hwfi : Integrable (fun x => w x * f x) μ)
    (hmean : ∫ x, f x ∂μ = 0) :
    0 ≤ ∫ x, w x * f x ∂μ := by sorry

end HedgeInv.Order
