-- Prove2me | Theorems.Thm_OAI_Erdos3_selected_cutoff_comparison_of_close_derivatives
-- name    : OAI.Erdos3.selected_cutoff_comparison_of_close_derivatives
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-08T10:43:49.829837+00:00
-- url     : https://prove2.me/theorems/d7c837b2-0ed2-4c77-bedc-f5cb3363534b
-- title:
--   Comparing image tests of two close maps under a smooth cutoff law
-- statement:
--   Let $\kappa,\iota$ be finite types with decidable equality, and let $\mu$ be a probability measure on $\mathbb R^\kappa$. Let $\chi,w\colon\mathbb R^\kappa\to\mathbb R$ with $\chi$ measurable and $0\le\chi\le1$, and $w$ of class $C^1$, compactly supported and nonnegative, such that the measures $w\,d\mathrm{vol}$ and $\chi\,d\mu$ coincide (`realDensityMeasure volume w = realDensityMeasure μ χ`, where `realDensityMeasure ν f` is $\nu$ with density $\max(f,0)$). Let $U,V\colon\mathbb R^\kappa\to\mathbb R^\iota$ be of class $C^2$, let $J\colon\mathbb R^\iota\to\mathbb R^\kappa$ be a continuous linear map with $\|J\|\le1$, and let $K,H,S\ge0$. Write `selectedDerivative U J x` for the linear map $DU(x)\circ J\colon\mathbb R^\iota\to\mathbb R^\iota$. Assume that for every $x$ in the topological support of $w$: $DU(x)\circ J$ is invertible, with $\|(DU(x)\circ J)^{-1}\|\le K$; $K\,\|DV(x)-DU(x)\|\le 1/2$; and the derivatives of $x\mapsto DU(x)\circ J$ and of $x\mapsto DV(x)\circ J$ have norm at most $H$ at $x$. Assume also $\sum_{j\in\kappa}\int|Dw(x)\,e_j|\,dx\le S$. Let $\varepsilon,\eta$ be reals with $\varepsilon>0$, $1-\eta\le\int w\,dx$, and $\operatorname{dist}(U(x),V(x))\le\varepsilon$ whenever $w(x)\ne0$. Then for every measurable $\varphi\colon\mathbb R^\iota\to\mathbb R$ with $|\varphi|\le1$, setting $B=1+2KS+|\kappa|\,(2K)^2H$,
--   $$\Big|\int\varphi(U(a))\,d\mu(a)-\int\varphi(V(a))\,d\mu(a)\Big|\le 2\eta+4|\iota|\sqrt{B\varepsilon},$$
--   where $\int\varphi(U(a))\,d\mu(a)$ is `mappedTest μ U φ`. Norms on $\mathbb R^\kappa$, $\mathbb R^\iota$ are Mathlib's sup norms and the corresponding operator norms; $e_j$ is the $j$-th standard basis vector.
--
--   Lean: `OAI.Erdos3.selected_cutoff_comparison_of_close_derivatives` in `lean/OAI/Combinatorics/Progressions/Estimates/JointBooleanStability.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B010`, `OAIErdos3B013` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/JointBooleanStability.lean#L68

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B010
import Definitions.Def_OAIErdos3B013

namespace OAI

section

namespace Erdos3

variable {I O : Type*} [Fintype I] [Fintype O]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem selected_cutoff_comparison_of_close_derivatives
    {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (μ : Measure (κ → ℝ)) [IsProbabilityMeasure μ]
    (χ w : (κ → ℝ) → ℝ) (hχ : Measurable χ) (hχ01 : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (hw : ContDiff ℝ 1 w) (hs : HasCompactSupport w) (hw0 : ∀ x, 0 ≤ w x)
    (hlaw : realDensityMeasure volume w = realDensityMeasure μ χ)
    (U V : (κ → ℝ) → (ι → ℝ)) (hU : ContDiff ℝ 2 U) (hV : ContDiff ℝ 2 V)
    (J : (ι → ℝ) →L[ℝ] (κ → ℝ)) (hJ : ‖J‖ ≤ 1) (K H S : ℝ≥0)
    (hinv : ∀ x ∈ tsupport w, (selectedDerivative U J x).IsInvertible)
    (hK : ∀ x ∈ tsupport w, ‖(selectedDerivative U J x).inverse‖ ≤ K)
    (hsmall : ∀ x ∈ tsupport w, (K : ℝ) * ‖fderiv ℝ V x - fderiv ℝ U x‖ ≤ 1 / 2)
    (hHU : ∀ x ∈ tsupport w, ‖fderiv ℝ (selectedDerivative U J) x‖ ≤ H)
    (hHV : ∀ x ∈ tsupport w, ‖fderiv ℝ (selectedDerivative V J) x‖ ≤ H)
    (hS : (∑ j, ∫ x, |fderiv ℝ w x (Pi.single j 1)|) ≤ S)
    {ε η : ℝ} (hε : 0 < ε) (hmass : 1 - η ≤ ∫ x, w x)
    (hclose : ∀ x, w x ≠ 0 → dist (U x) (V x) ≤ ε)
    (φ : (ι → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    let B := 1 + 2 * (K : ℝ) * S + (Fintype.card κ : ℝ) * ((2 * (K : ℝ)) ^ 2 * H)
    |mappedTest μ U φ - mappedTest μ V φ| ≤
      2 * η + 4 * (Fintype.card ι : ℝ) * Real.sqrt (B * ε) := by
  sorry

end Erdos3
end
end OAI
