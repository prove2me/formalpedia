-- Prove2me | Theorems.Thm_HedgeInv_Order_lemma2_ii
-- name    : HedgeInv.Order.lemma2_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:21:49.23041+00:00
-- url     : https://prove2.me/theorems/44ee7183-9d64-44a1-bdc3-c866a8fa3ce9
-- title:
--   Lemma 2(ii), p. 118 (weak form) — f decreasing with E[f(X)] = 0 and w increasing, nonnegative ⇒ E[w(X)f(X)] ≤ 0
-- statement:
--   Let $X$ be a real random variable with law $\mu$. Let $f:\mathbb R\to\mathbb R$ be nonincreasing with $f(X)$ integrable and $E[f(X)]=0$. Let $w:\mathbb R\to\mathbb R$ be nondecreasing and nonnegative, with $w(X)f(X)$ integrable. Then
--   $$E[w(X)\,f(X)]\ \le\ 0.$$
--
--   This is the companion of Lemma 2(i): functions that move in opposite directions are nonpositively correlated. In the paper it gives the sign of the second term of (25).
--
--   **Formalization Note.** The paper prints a strict inequality $E[w(X)f(X)]<0$, which fails for $w\equiv1$. The weak inequality is stated here, and it is the form the proof of Proposition 7 uses.
-- source:
--   Gaur & Seshadri, Hedging Inventory Risk Through Market Instruments, Manuf. Serv. Oper. Manag. 7(2) (2005), p. 118, Lemma 2(ii)

import Mathlib

namespace HedgeInv.Order

open MeasureTheory

/-- Lemma 2(ii), p. 118, in the weak form: if `f` is nonincreasing with `E[f(X)] = 0` and `w` is
nondecreasing and nonnegative, then `E[w(X) f(X)] ≤ 0`. `μ` is the law of `X`. (The printed
strict inequality fails for `w ≡ 1`.) -/
theorem lemma2_ii (μ : Measure ℝ) [IsProbabilityMeasure μ] (f w : ℝ → ℝ)
    (hf : Antitone f) (hw : Monotone w) (hw0 : ∀ x, 0 ≤ w x)
    (hfi : Integrable f μ) (hwfi : Integrable (fun x => w x * f x) μ)
    (hmean : ∫ x, f x ∂μ = 0) :
    ∫ x, w x * f x ∂μ ≤ 0 := by sorry

end HedgeInv.Order
