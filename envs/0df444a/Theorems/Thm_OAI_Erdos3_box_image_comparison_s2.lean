-- Prove2me | Theorems.Thm_OAI_Erdos3_box_image_comparison_s2
-- name    : OAI.Erdos3.box_image_comparison_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:29:23.309634+00:00
-- url     : https://prove2.me/theorems/21ea2f74-5de5-441e-8494-ddc3fe10b4d8
-- title:
--   Comparing the averages of a bounded test over the images of two nearby maps with translation-Lipschitz images
-- statement:
--   Let $\Omega$ be a measurable space and $\iota$ a finite type with decidable equality; equip $\mathbb{R}^\iota$ with its sup distance. Let $\mu$ be a finite measure on $\Omega$ with $\mu(\Omega) \le 1$. For a map $U : \Omega \to \mathbb{R}^\iota$ and a test $\varphi : \mathbb{R}^\iota \to \mathbb{R}$, write `mappedTest μ U φ` $= \int \varphi(U(a))\, d\mu(a)$ (defined by OpenAI). Say that $U$ satisfies `ImageTranslationBound μ U H` (defined by OpenAI), for $H \in \mathbb{R}_{\ge 0}$, if for every measurable $\varphi$ with $|\varphi(x)| \le 1$ for all $x$ and every $z \in \mathbb{R}^\iota$,
--   $$\bigl| \texttt{mappedTest}(\mu, U, x \mapsto \varphi(x + z)) - \texttt{mappedTest}(\mu, U, \varphi) \bigr| \le H \cdot \operatorname{dist}(z, 0).$$
--
--   Let $U, V : \Omega \to \mathbb{R}^\iota$ be measurable, and let $H_U, H_V \in \mathbb{R}_{\ge 0}$ be such that `ImageTranslationBound μ U H_U` and `ImageTranslationBound μ V H_V` hold. Let $\varepsilon \ge 0$ with $\operatorname{dist}(U(a), V(a)) \le \varepsilon$ for $\mu$-almost every $a$. Let $\delta > 0$ and let $\varphi : \mathbb{R}^\iota \to \mathbb{R}$ be measurable with $|\varphi(x)| \le 1$ for all $x$. Then
--   $$\bigl| \texttt{mappedTest}(\mu, U, \varphi) - \texttt{mappedTest}(\mu, V, \varphi) \bigr| \le (H_U + H_V)\,\delta + \frac{2\,|\iota|\,\varepsilon}{\delta}.$$
--
--   Lean: `OAI.Erdos3.box_image_comparison_s2`, which states OpenAI's `OAI.Erdos3.box_image_comparison` (in `lean/OAI/Combinatorics/Progressions/Geometry/BoxImageComparison.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B048` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/BoxImageComparison.lean (declaration OAI.Erdos3.box_image_comparison)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B048

section

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]

theorem box_image_comparison_s2 [DecidableEq ι] (μ : Measure Ω) [IsFiniteMeasure μ]
    (hmass : μ.real Set.univ ≤ 1) (U V : Ω → (ι → ℝ)) (hU : Measurable U) (hV : Measurable V)
    (H_U H_V : ℝ≥0) (hTU : ImageTranslationBound μ U H_U) (hTV : ImageTranslationBound μ V H_V)
    {ε : ℝ} (hε : 0 ≤ ε) (hclose : ∀ᵐ a ∂μ, dist (U a) (V a) ≤ ε)
    (δ : ℝ) (hδ : 0 < δ) (φ : (ι → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    |mappedTest μ U φ - mappedTest μ V φ| ≤
      ((H_U : ℝ) + H_V) * δ + 2 * (Fintype.card ι : ℝ) * ε / δ := by
  sorry

end Erdos3

end

end OAI
end
