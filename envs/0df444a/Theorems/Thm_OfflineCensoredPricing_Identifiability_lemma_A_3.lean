-- Prove2me | Theorems.Thm_OfflineCensoredPricing_Identifiability_lemma_A_3
-- name    : OfflineCensoredPricing.Identifiability.lemma_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:31:57.627715+00:00
-- url     : https://prove2.me/theorems/227d1009-8556-4b46-afb7-c48177b260ef
-- title:
--   Lemma A.3, p. 35 — (Qin et al. 2019, Lemma 14) uniform deviation bound 2e^{−2nε²/(U−L)²} for bounded functions monotone in the sample
-- statement:
--   Let $X_1, \dots, X_n$ be i.i.d. real random variables with law $\mu$ and values in $\mathcal X \subseteq \mathbb R$, and let $\mathcal Y \subseteq \mathbb R$. Suppose $f(x, y) : \mathcal X \times \mathcal Y \to [L, U]$ is measurable and monotone in $x \in \mathcal X$ for any given $y \in \mathcal Y$. Then for any $\varepsilon > 0$,
--   $$\mathbb P\Big[\sup_{y\in\mathcal Y}\Big|\frac1n\sum_{i=1}^n f(X_i, y) - \mathbb E[f(X_1, y)]\Big| \le \varepsilon\Big] \ge 1 - 2e^{-\frac{2n\varepsilon^2}{(U-L)^2}}.$$
--
--   This generalizes the Dvoretzky–Kiefer–Wolfowitz inequality from indicators of half-lines to bounded monotone functions. The paper uses it to obtain uniform-in-price bounds on the empirical revenue (Lemma D.1).
--
--   **Formalization Note** "Monotone in $x$" means nondecreasing or nonincreasing on $\mathcal X$, possibly depending on $y$. Measurability is required of each section $x \mapsto f(x, y)$, $y \in \mathcal Y$, which is what defines $\mathbb E[f(X_1, y)]$. The $X_i$ lie in $\mathcal X$ almost surely. The statement bounds the outer probability of $\{\exists y \in \mathcal Y,\ |\frac1n\sum_i f(X_i,y) - \mathbb E f(X_1,y)| > \varepsilon\}$.
-- source:
--   Bu, Simchi-Levi & Wang, SSRN 3619625 (PDF of 2021-08-23), p. 35, Lemma A.3 (citing Lemma 14 of Qin et al. 2019)

import Mathlib

namespace OfflineCensoredPricing.Identifiability

open MeasureTheory

/-- **Lemma A.3** (Lemma 14 in Qin et al. 2019; p. 35). Let `X₁, …, Xₙ` be i.i.d. random variables
(law `μ`, values in `𝒳 ⊆ ℝ` almost surely) and `𝒴 ⊆ ℝ`. Suppose `f(x, y) : 𝒳 × 𝒴 → [L, U]` is
measurable and monotone in `x ∈ 𝒳` for any given `y ∈ 𝒴`. Then for any `ε > 0`,
`P[sup_{y ∈ 𝒴} |(1/n) ∑ᵢ f(Xᵢ, y) − E[f(X₁, y)]| ≤ ε] ≥ 1 − 2e^{−2nε²/(U−L)²}`, stated as an upper bound
on the outer probability of the failure event. "Monotone" is nondecreasing or nonincreasing, possibly
depending on `y`. -/
theorem lemma_A_3 (μ : Measure ℝ) [IsProbabilityMeasure μ] (X Y : Set ℝ) (hX : ∀ᵐ x ∂μ, x ∈ X)
    (f : ℝ → ℝ → ℝ) (hfm : ∀ y ∈ Y, Measurable (fun x => f x y)) {L U : ℝ}
    (hf : ∀ x ∈ X, ∀ y ∈ Y, f x y ∈ Set.Icc L U)
    (hmono : ∀ y ∈ Y, MonotoneOn (fun x => f x y) X ∨ AntitoneOn (fun x => f x y) X)
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Measure.pi (fun _ : Fin n => μ)
        {ω | ∃ y ∈ Y, ε < |(∑ i, f (ω i) y) / (n : ℝ) - ∫ x, f x y ∂μ|} ≤
      ENNReal.ofReal (2 * Real.exp (-(2 * (n : ℝ) * ε ^ 2 / (U - L) ^ 2))) := by sorry

end OfflineCensoredPricing.Identifiability
