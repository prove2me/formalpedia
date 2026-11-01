-- Prove2me | Theorems.Thm_MeanFieldContest_lemma_3_9
-- name    : MeanFieldContest.lemma_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:55:15.689026+00:00
-- url     : https://prove2.me/theorems/62aa7c1d-bb23-4eec-8a2d-f6bf599e9a55
-- title:
--   Lemma 3.9 — the affine $\ell_1$ touching $\Phi(F)$ on $A$ and at the $w_y$
-- statement:
--   Let $R$ be a reward function, $\mu<\bar\mu_\infty$ and $F$ a mean field equilibrium. Then $w_y<\bar w_F$ for all $y\in J(g)$. Moreover there is a strictly increasing affine function $\ell_1\ge\Phi(F)$ with $\ell_1(1)=\Phi(F)^{conc}(1)$ and
--
--   1. $\ell_1(\bar w_F)=g(1)$,
--   2. $\Phi(F)=\ell_1\wedge g(1)$ on $A$,
--   3. $\Phi(F)(w_y)=\ell_1(w_y)$ for all $y\in J(g)$.
--
--   So on the scale $w=h(x)$ an equilibrium is pinned to one line, up to flat stretches, which is what makes it unique.
--
--   Differences from the source:
--   - encoding: R : [0,1] → ℝ₊ → R : ℝ → ℝ with every condition stated on [0,1]; reason: no object reads R outside [0,1]
--   - encoding: a randomized stopping time τ < ∞ of the absorbed process → a stopping time of a filtration 𝔾 for which W is a Brownian motion, finite a.s., on a probability space Ω : Type, with a.e.-measurable stopping position; reason: a randomized stopping time is a stopping time of a larger filtration; the measurability only excludes the junk value of Measure.map; the law is what is quantified over
--   - encoding: concave envelope on ℝ₊, with F∘h⁻¹ and ξ^F∘h⁻¹ on [0, h(∞)] → concOn on D = [0, h(∞)] ∩ ℝ (supremum over finite convex combinations), with F∘h⁻¹(h(∞)) := 1 and ξ^F∘h⁻¹(h(∞)) := g(1) when h(∞) < ∞; reason: D is ℝ₊ for µ ≤ 0 and the functions are not defined beyond h(∞) for µ > 0; the values at h(∞) are the limits; for these bounded functions the supremum is the smallest concave majorant at points of D
--   - reading: ℓ₁(w̄_F) = g(1) → w̄_F is a real number w with ℓ₁(w) = g(1); reason: ℓ₁ is affine on ℝ, so the printed equation presupposes that w̄_F is finite; the proof obtains w̄_F = ℓ₁⁻¹(g(1)). The stronger reading is taken
-- source:
--   Nutz–Zhang, Mean Field Contest with Singularity, arXiv:2103.04219v1, Lemma 3.9, p.15

import Mathlib
import Definitions.Def_TractableComposite_concOn
import Definitions.Def_MeanFieldContest_Model
import Definitions.Def_MeanFieldContest_EnvelopeObjects

open MeasureTheory ProbabilityTheory Set

namespace MeanFieldContest

/-- **Lemma 3.9**, arXiv:2103.04219v1, p.15. Let `F` be a mean field equilibrium. Then `w_y < w̄_F` for all `y ∈ J(g)`.
Moreover there is a strictly increasing affine `ℓ₁ ≥ Φ(F)` with `ℓ₁(1) = Φ(F)^conc(1)` and
(i) `ℓ₁(w̄_F) = g(1)`, (ii) `Φ(F) = ℓ₁ ∧ g(1)` on `A`, (iii) `Φ(F)(w_y) = ℓ₁(w_y)` for all `y ∈ J(g)`.

**Formalization Note.** `ℓ₁(w) = a w + b` with `a > 0`, and `ℓ₁ ≥ Φ(F)` on `D`. Clause (i) asserts
that `w̄_F` is a real number, which is what makes `ℓ₁(w̄_F)` meaningful (the proof's `w̄₁ = ℓ₁⁻¹(g(1))`
equals `w̄_F`). -/
theorem lemma_3_9 {x₀ μ σ : ℝ} {R : ℝ → ℝ} {F : Measure ℝ}
    (hx₀ : 0 < x₀) (hσ : 0 < σ) (hR : IsRewardFunction R) (hμ : μ < muBarInfty R x₀ σ)
    (hF : IsMFE x₀ μ σ R F) :
    (∀ y ∈ jumpSet R, ((wLevel x₀ μ σ F y : ℝ) : EReal) < wBar x₀ μ σ R F) ∧
    ∃ a b : ℝ, 0 < a ∧ (∀ w ∈ hDomain x₀ μ σ, Phi x₀ μ σ R F w ≤ a * w + b) ∧
      a * 1 + b = TractableComposite.concOn (hDomain x₀ μ σ) (Phi x₀ μ σ R F) 1 ∧
      (∃ w : ℝ, (w : EReal) = wBar x₀ μ σ R F ∧ a * w + b = g R 1) ∧
      (∀ w ∈ unionA x₀ μ σ R F, Phi x₀ μ σ R F w = min (a * w + b) (g R 1)) ∧
      (∀ y ∈ jumpSet R,
        Phi x₀ μ σ R F (wLevel x₀ μ σ F y) = a * wLevel x₀ μ σ F y + b) := by sorry

end MeanFieldContest
