-- Prove2me | Theorems.Thm_OAI_Erdos3_cutoff_box_image_comparison_sqrt
-- name    : OAI.Erdos3.cutoff_box_image_comparison_sqrt
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-08T10:47:40.742007+00:00
-- url     : https://prove2.me/theorems/b0608720-d186-4521-9029-183b49baf25d
-- title:
--   Comparing two box images under a cutoff weight, with a square-root error
-- statement:
--   Let $\Omega$ be a measurable space and $\iota$ a finite type with decidable equality. Let $\mu$ be a probability measure on $\Omega$, and $w : \Omega\to\mathbb{R}$ a measurable function with $w(a)\in[0,1]$ for all $a$. Let $U,V : \Omega\to\mathbb{R}^\iota$ be measurable, and let $B\ge 0$ be a real number (an element of $\mathbb{R}_{\ge0}$) with $0<B$. Write $\nu$ for `realDensityMeasure μ w`, the measure with density $a\mapsto\max(w(a),0)$ with respect to $\mu$. Assume `ImageTranslationBound ν U (|ι|·B)` and `ImageTranslationBound ν V (|ι|·B)`, where `ImageTranslationBound ν U H` is the predicate: for every measurable $\varphi:\mathbb{R}^\iota\to\mathbb{R}$ with $|\varphi|\le 1$ everywhere and every $z\in\mathbb{R}^\iota$, $\big|\int\varphi(U(a)+z)\,d\nu(a)-\int\varphi(U(a))\,d\nu(a)\big|\le H\cdot\mathrm{dist}(z,0)$ (distance in the sup metric on $\mathbb{R}^\iota$). Let $\varepsilon,\eta$ be real numbers with $0<\varepsilon$, $\int(1-w(a))\,d\mu(a)\le\eta$, and $\mathrm{dist}(U(a),V(a))\le\varepsilon$ for $\nu$-almost every $a$. Then for every measurable $\varphi:\mathbb{R}^\iota\to\mathbb{R}$ with $|\varphi(x)|\le 1$ for all $x$,
--   $$\big|\texttt{mappedTest}\ \mu\ U\ \varphi-\texttt{mappedTest}\ \mu\ V\ \varphi\big|\le 2\eta+4\,|\iota|\sqrt{B\varepsilon},$$
--   where `mappedTest μ U φ` is $\int\varphi(U(a))\,d\mu(a)$ (with respect to $\mu$, not $\nu$).
--
--   Lean: `OAI.Erdos3.cutoff_box_image_comparison_sqrt` in `lean/OAI/Combinatorics/Progressions/Geometry/CutoffBoxImageComparison.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B010` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/CutoffBoxImageComparison.lean#L64

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B010

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]

theorem cutoff_box_image_comparison_sqrt (μ : Measure Ω) [IsProbabilityMeasure μ]
    (w : Ω → ℝ) (hw : Measurable w) (hw01 : ∀ a, w a ∈ Set.Icc (0 : ℝ) 1)
    (U V : Ω → (ι → ℝ)) (hU : Measurable U) (hV : Measurable V)
    (B : ℝ≥0) (hB : 0 < (B : ℝ))
    (hTU : ImageTranslationBound (realDensityMeasure μ w) U ((Fintype.card ι : ℝ≥0) * B))
    (hTV : ImageTranslationBound (realDensityMeasure μ w) V ((Fintype.card ι : ℝ≥0) * B))
    {ε η : ℝ} (hε : 0 < ε) (hcut : (∫ a, 1 - w a ∂μ) ≤ η)
    (hclose : ∀ᵐ a ∂realDensityMeasure μ w, dist (U a) (V a) ≤ ε)
    (φ : (ι → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    |mappedTest μ U φ - mappedTest μ V φ| ≤
      2 * η + 4 * (Fintype.card ι : ℝ) * Real.sqrt ((B : ℝ) * ε) := by
  sorry

end Erdos3
end
end OAI
