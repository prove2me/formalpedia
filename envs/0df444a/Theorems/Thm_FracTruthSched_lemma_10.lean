-- Prove2me | Theorems.Thm_FracTruthSched_lemma_10
-- name    : FracTruthSched.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:28:15.029315+00:00
-- url     : https://prove2.me/theorems/0f2021aa-fb7e-4a0a-bedf-5326195cf06f
-- title:
--   Lemma 10 — uniqueness of the Laplace transform on $\mathbb R^4_{\ge0}$
-- statement:
--   Let $F:\mathbb R^4_{\ge0}\to\mathbb R$ be measurable, with $|F(r)|\le\sum_{\nu=1}^4 r_\nu$. If
--   $$\int_{\mathbb R^4_{\ge0}}F(r)\,e^{-\theta\cdot r}\,dr=0\qquad\text{for every }\theta\in(0,\infty)^4,$$
--   then $F=0$ almost everywhere on $\mathbb R^4_{\ge0}$.
--
--   This is the instance of the uniqueness theorem for the multivariate Laplace transform used in Step 4 of the proof of two-task separation. The growth bound makes all the integrals absolutely convergent.
--
--   **Formalization Note.** $F$ is a function on $\mathbb R^4$ whose values off the orthant are irrelevant; measure is Lebesgue measure restricted to the closed orthant.
--
--   Differences from the source:
--   - generalization: F measurable → F almost everywhere strongly measurable for Lebesgue measure on the orthant; reason: covers both Borel and Lebesgue measurability; a weaker hypothesis, so the statement specializes to the source's
--   - encoding: F : ℝ⁴_{≥0} → ℝ → F : (Fin 4 → ℝ) → ℝ with hypotheses and conclusion on Set.Ici 0; reason: values off the orthant never enter
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, Lemma 10, App. C, p.28

import Mathlib

set_option autoImplicit false

namespace FracTruthSched

open MeasureTheory

/-- **Lemma 10 (uniqueness of the Laplace transform)** (Anastasiadis et al., arXiv:2611.06642v1,
Lemma 10, App. C, p.28). Let `F : ℝ⁴_{≥0} → ℝ` be measurable, with `|F(r)| ≤ Σ_{ν=1}^4 r_ν`. If
`∫_{ℝ⁴_{≥0}} F(r) e^{−θ·r} dr = 0` for every `θ ∈ (0, ∞)⁴`, then `F = 0` almost everywhere.

**Formalization Note.** `ℝ⁴_{≥0}` is `Set.Ici 0` in `Fin 4 → ℝ` with Lebesgue measure `volume`;
`F` is a function on `Fin 4 → ℝ` whose values off the orthant are irrelevant. Measurability is taken
as a.e. strong measurability for the restricted measure, which covers both Borel and Lebesgue
measurability. The integrals are absolutely convergent by the growth bound, so the hypothesis is not
satisfied by Lean's junk value of a non-integrable Bochner integral. -/
theorem lemma_10 (F : (Fin 4 → ℝ) → ℝ)
    (hF : AEStronglyMeasurable F (volume.restrict (Set.Ici (0 : Fin 4 → ℝ))))
    (hgrowth : ∀ r ∈ Set.Ici (0 : Fin 4 → ℝ), |F r| ≤ ∑ ν, r ν)
    (hL : ∀ θ : Fin 4 → ℝ, (∀ ν, 0 < θ ν) →
      ∫ r in Set.Ici (0 : Fin 4 → ℝ), F r * Real.exp (-∑ ν, θ ν * r ν) = 0) :
    F =ᵐ[volume.restrict (Set.Ici (0 : Fin 4 → ℝ))] 0 := by sorry

end FracTruthSched
