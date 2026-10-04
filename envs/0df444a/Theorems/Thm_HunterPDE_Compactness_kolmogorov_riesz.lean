-- Prove2me | Theorems.Thm_HunterPDE_Compactness_kolmogorov_riesz
-- name    : HunterPDE.Compactness.kolmogorov_riesz
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T07:55:37.623966+00:00
-- url     : https://prove2.me/theorems/f84c9343-8b0e-4a85-ab97-df3235a89ad4
-- title:
--   Theorem 1.15 — Kolmogorov–Riesz compactness criterion in Lᵖ(ℝⁿ)
-- statement:
--   Let $1 \le p < \infty$. A subset $\mathcal{F}$ of $L^p(\mathbb{R}^n)$ is precompact (its closure is compact) if and only if:
--
--   1. there exists $M$ such that $\|f\|_{L^p} \le M$ for all $f \in \mathcal{F}$;
--   2. for every $\varepsilon > 0$ there exists $R$ such that $\big(\int_{|x|>R} |f(x)|^p \, dx\big)^{1/p} < \varepsilon$ for all $f \in \mathcal{F}$;
--   3. for every $\varepsilon > 0$ there exists $\delta > 0$ such that if $|h| < \delta$,
--   $$\Big(\int_{\mathbb{R}^n} |f(x+h) - f(x)|^p \, dx\Big)^{1/p} < \varepsilon \qquad \text{for all } f \in \mathcal{F}.$$
--
--   This is the $L^p$ analogue of the Arzelà–Ascoli theorem: bounded, tight and $L^p$-equicontinuous. The Rellich–Kondrachov theorem is proved by verifying these three conditions. The notes cite it without proof.
--
--   **Formalization Note.** $\mathcal{F}$ is a set in Mathlib's `Lp ℝ p volume` on `EuclideanSpace ℝ (Fin n)`, with `p : ℝ≥0∞`, `1 ≤ p` and `p ≠ ∞`. Both $L^p$ integrals are written with `eLpNorm`, which for finite $p \ge 1$ equals $(\int |\cdot|^p)^{1/p}$, and $\varepsilon$ is compared through `ENNReal.ofReal`.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), pp. 6–7, Theorem 1.15

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace HunterPDE.Compactness

/-- Theorem 1.15 of Hunter, *Notes on PDEs* (revised 6/18/2014), pp. 6–7 (Kolmogorov–Riesz,
Riesz–Tamarkin, Fréchet–Kolmogorov): for `1 ≤ p < ∞`, a subset `F` of `Lᵖ(ℝⁿ)` is precompact
(its closure is compact) if and only if
(1) `F` is bounded: `‖f‖_{Lᵖ} ≤ M` for all `f ∈ F`;
(2) `F` is tight: for every `ε > 0` there is `R` with `(∫_{|x|>R} |f|ᵖ dx)^{1/p} < ε` for all `f ∈ F`;
(3) `F` is `Lᵖ`-equicontinuous: for every `ε > 0` there is `δ > 0` such that `|h| < δ` implies
`(∫_{ℝⁿ} |f(x + h) − f(x)|ᵖ dx)^{1/p} < ε` for all `f ∈ F`.
The `Lᵖ` norms over `{|x| > R}` and of the translation difference are written with `eLpNorm`,
which for `1 ≤ p < ∞` is `(∫ |·|ᵖ)^{1/p}`. -/
theorem kolmogorov_riesz {n : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (F : Set (Lp ℝ p (volume : Measure (EuclideanSpace ℝ (Fin n))))) :
    IsCompact (closure F) ↔
      ((∃ M : ℝ, ∀ f ∈ F, ‖f‖ ≤ M) ∧
        (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ f ∈ F,
          eLpNorm (f : EuclideanSpace ℝ (Fin n) → ℝ) p
            (volume.restrict {x : EuclideanSpace ℝ (Fin n) | R < ‖x‖}) < ENNReal.ofReal ε) ∧
        (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : EuclideanSpace ℝ (Fin n), ‖h‖ < δ → ∀ f ∈ F,
          eLpNorm (fun x => (f : EuclideanSpace ℝ (Fin n) → ℝ) (x + h) -
            (f : EuclideanSpace ℝ (Fin n) → ℝ) x) p volume < ENNReal.ofReal ε)) := by sorry

end HunterPDE.Compactness
