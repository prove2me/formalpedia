-- Prove2me | Theorems.Thm_OAI_Erdos3_imageTranslationBound_of_inverse_budget_s2
-- name    : OAI.Erdos3.imageTranslationBound_of_inverse_budget_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:29:02.329345+00:00
-- url     : https://prove2.me/theorems/59e48484-65e9-4b30-afd9-b30ce30b3dd6
-- title:
--   Translation stability of the image of a smooth density under a map with a controlled selected inverse derivative
-- statement:
--   Let $\kappa, \iota$ be finite types with decidable equality. Let $U : \mathbb{R}^\kappa \to \mathbb{R}^\iota$ be $C^2$, and let $J : \mathbb{R}^\iota \to \mathbb{R}^\kappa$ be a continuous linear map with operator norm $\lVert J \rVert \le 1$. Let $w : \mathbb{R}^\kappa \to \mathbb{R}$ be $C^1$ with compact support, $w \ge 0$, and $\int |w| \le 1$ (Lebesgue measure). Let $K, H, S, B \in \mathbb{R}_{\ge 0}$, and write $\Delta(x)$ = `selectedDerivative U J x` $= DU(x) \circ J$, a linear map $\mathbb{R}^\iota \to \mathbb{R}^\iota$. Suppose that for every $x$ in the topological support of $w$: $\Delta(x)$ is invertible, $\lVert \Delta(x)^{-1} \rVert \le K$, and $\lVert D\Delta(x) \rVert \le H$ (the derivative of $x \mapsto \Delta(x)$). Suppose also
--   $$\sum_{j \in \kappa} \int \bigl| Dw(x)(e_j) \bigr|\, dx \le S \qquad\text{and}\qquad K S + |\kappa|\,(K^2 H) \le B,$$
--   where $e_j$ is the $j$-th standard basis vector.
--
--   Then `ImageTranslationBound (realDensityMeasure volume w) U (|ι| · B)` holds: writing $\mu$ for the measure with density $w$ with respect to Lebesgue measure, for every measurable $\varphi : \mathbb{R}^\iota \to \mathbb{R}$ with $|\varphi| \le 1$ everywhere and every $z \in \mathbb{R}^\iota$,
--   $$\Bigl| \int \varphi(U(x) + z)\, d\mu(x) - \int \varphi(U(x))\, d\mu(x) \Bigr| \le |\iota|\, B\cdot \lVert z \rVert$$
--   (with the sup norm on $\mathbb{R}^\iota$, the distance used by Lean on function spaces).
--
--   Lean: `OAI.Erdos3.imageTranslationBound_of_inverse_budget_s2`, which states OpenAI's `OAI.Erdos3.imageTranslationBound_of_inverse_budget` (in `lean/OAI/Combinatorics/Progressions/Dynamics/BudgetedOpenImageComparison.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B037`, `OAIE3v2B048` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Dynamics/BudgetedOpenImageComparison.lean (declaration OAI.Erdos3.imageTranslationBound_of_inverse_budget)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B037
import Definitions.Def_OAIE3v2B048

section

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem imageTranslationBound_of_inverse_budget_s2
    {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (U : (κ → ℝ) → (ι → ℝ)) (hU : ContDiff ℝ 2 U)
    (J : (ι → ℝ) →L[ℝ] (κ → ℝ)) (hJ : ‖J‖ ≤ 1)
    (w : (κ → ℝ) → ℝ) (hw : ContDiff ℝ 1 w) (hs : HasCompactSupport w)
    (hw0 : ∀ x, 0 ≤ w x) (hmass : (∫ x, |w x|) ≤ 1)
    (K H S B : ℝ≥0)
    (hinv : ∀ x ∈ tsupport w, (selectedDerivative U J x).IsInvertible)
    (hK : ∀ x ∈ tsupport w, ‖(selectedDerivative U J x).inverse‖ ≤ K)
    (hH : ∀ x ∈ tsupport w, ‖fderiv ℝ (selectedDerivative U J) x‖ ≤ H)
    (hS : (∑ j, ∫ x, |fderiv ℝ w x (Pi.single j 1)|) ≤ S)
    (hB : (K : ℝ) * S + (Fintype.card κ : ℝ) * ((K : ℝ) ^ 2 * H) ≤ B) :
    ImageTranslationBound (realDensityMeasure volume w) U ((Fintype.card ι : ℝ≥0) * B) := by
  sorry

end Erdos3

end

end OAI
end
