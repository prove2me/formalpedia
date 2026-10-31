-- Prove2me | Theorems.Thm_FuchsThesis_HonestExpert_lemma_2_1
-- name    : FuchsThesis.HonestExpert.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:20:56.031879+00:00
-- url     : https://prove2.me/theorems/f2afecda-04b7-4c29-8ac8-c18d815e225c
-- title:
--   Lemma 2.1 (Lebesgue) — a monotone function on $[a,b]$ is differentiable a.e. and $\int_a^b f'\le f(b)-f(a)$
-- statement:
--   Let $a \le b$ be real numbers and let $f$ be a real-valued function that is monotonically nondecreasing on $[a, b]$. Then:
--
--   1. $f$ is differentiable at almost every point of $[a, b]$ (with respect to Lebesgue measure);
--   2. the derivative $f'$ is measurable;
--   3. $f'$ is integrable on $[a, b]$ and
--   $$\int_a^b f'(x)\,dx \;\le\; f(b) - f(a) .$$
--
--   This is Lebesgue's differentiation theorem for monotone functions, as quoted in the thesis from Royden's *Real Analysis*. The thesis uses only clause 1: if an honest payoff $F_1$ were not differentiable at one point $p$, the nondecreasing $F_2$ would be nowhere differentiable on $(0, 1 - p)$, which clause 1 rules out.
--
--   **Formalization Note** $f$ is a function on $\mathbb R$ whose values outside $[a,b]$ are unconstrained; differentiability and the derivative at interior points depend only on $f$ on $[a,b]$. The integral is the interval (Bochner) integral, and integrability of $f'$ is stated explicitly so that the inequality is not satisfied by the default value $0$ that Lean assigns to the integral of a non-integrable function.
--
--   Differences from the source:
--   - reading: "increasing" → monotonically nondecreasing (MonotoneOn); reason: the thesis applies the lemma to the monotonically nondecreasing F₁, F₂, and Royden's "increasing" means nondecreasing
--   - generalization: f′ measurable (as a function on [a, b]) → f′ = deriv f measurable as a function on all of ℝ; reason: measurability on ℝ implies measurability of the restriction to [a, b]
--   - encoding: ∫_a^b f′ (Lebesgue integral of a nonnegative function, finite) → IntervalIntegrable (deriv f) on [a, b] together with the interval integral bound; f on [a, b] → f : ℝ → ℝ, monotone on [a, b]; reason: Lean's Bochner integral is 0 for non-integrable integrands, so finiteness is stated; any f on [a, b] extends to ℝ and the extension does not affect any clause
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, §2.3.1, Lemma 2.1, p.23 (PDF p.32), citing Royden, Real Analysis, p.96

import Mathlib

open MeasureTheory

namespace FuchsThesis.HonestExpert

/-- **Lemma 2.1 (Lebesgue's theorem on monotone functions).**
Fuchs, *Distinguishability and Accessible Information in Quantum Theory*, arXiv:quant-ph/9601020v1,
§2.3.1, Lemma 2.1, p.23 (PDF p.32), citing Royden [55, p.96]: "Let f be an increasing real-valued
function on the interval [a, b]. Then f is differentiable almost everywhere. The derivative f′ is
measurable, and ∫_a^b f′(x) dx ≤ f(b) − f(a)."

For reals `a ≤ b` and `f : ℝ → ℝ` monotonically nondecreasing on `[a, b]`:
1. `f` is differentiable at almost every point of `[a, b]` (Lebesgue measure);
2. the derivative `f′` is measurable;
3. `f′` is integrable on `[a, b]` and `∫_a^b f′(x) dx ≤ f(b) − f(a)`.

**Formalization Note.** "Increasing" is read as nondecreasing (`MonotoneOn`), as the thesis applies
the lemma to the monotonically nondecreasing `F₁, F₂`. `f` is typed on `ℝ`; its values outside
`[a, b]` are unconstrained, and differentiability and the derivative at interior points depend only
on `f` on `[a, b]`. The integral is Mathlib's interval (Bochner) integral; the integrability of `f′`
is stated explicitly, so that clause 3 is not satisfied by the junk value `0` of a non-integrable
integrand (for the nonnegative `f′` this is the finiteness implicit in the page's Lebesgue
integral). -/
theorem lemma_2_1 {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : MonotoneOn f (Set.Icc a b)) :
    (∀ᵐ x ∂(volume.restrict (Set.Icc a b)), DifferentiableAt ℝ f x) ∧
      Measurable (deriv f) ∧
      IntervalIntegrable (deriv f) volume a b ∧
      ∫ x in a..b, deriv f x ≤ f b - f a := by sorry

end FuchsThesis.HonestExpert
