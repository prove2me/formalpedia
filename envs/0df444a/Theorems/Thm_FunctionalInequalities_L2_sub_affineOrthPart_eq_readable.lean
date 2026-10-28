-- Prove2me | Theorems.Thm_FunctionalInequalities_L2_sub_affineOrthPart_eq_readable
-- name    : FunctionalInequalities.L2.sub_affineOrthPart_eq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:23.135503+00:00
-- url     : https://prove2.me/theorems/816eb15b-7e4e-4f5f-a7bc-08e3b253675d
-- title:
--   Subtracting an Affine-Orthogonal Part From an Orthogonal Function
-- statement:
--   This lemma gives an exact function identity for affine subtraction when the first function is orthogonal to affine functions.
--
--   Let $n\in\mathbb N$, $E=\mathbb R^n$ (`EuclideanSpace ℝ (Fin n)`), and $\mu$ a probability measure on $E$. Assume:
--   1. $\operatorname{id}\in L^2(\mu)$.
--   2. $f,g:E\to\mathbb R$ belong to $L^2(\mu)$.
--   3. $\int f\,d\mu=0$ and $\int\langle u,x\rangle f(x)\,d\mu=0$ for every $u\in E$.
--
--   For any function $h$, write $\widetilde h=$ `affineOrthPart` $\mu\ h$, defined by subtracting $\int h\,d\mu$ and $\sum_j(\int\langle e_j,y\rangle h(y)\,d\mu(y))\langle e_j,\cdot\rangle$, where $(e_j)$ is the standard orthonormal basis. Then, as functions on $E$,
--   $$
--   f-\widetilde g=\widetilde{\,f-g\,}.
--   $$
--
--   This identity is useful for comparing affine-subtracted approximations. It is pointwise, not merely almost everywhere, and requires neither centering nor identity covariance of $\mu$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.L2`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sub_affineOrthPart_eq (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
--       (hμ2 : MemLp id 2 μ) {f g : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f 2 μ)
--       (hf0 : ∫ x, f x ∂μ = 0) (hfx : ∀ u, ∫ x, ⟪u, x⟫ * f x ∂μ = 0) (hg : MemLp g 2 μ) :
--       f - affineOrthPart μ g = affineOrthPart μ (f - g)
--   ```
--
--   **Module navigation**
--
--   Module: [`L2/AffineDecomposition`](https://prove2.me/theorems/78e08949-2f1e-4981-ab20-7428c8af6614).
--
--   Previous: [`integral_inner_mul_affineOrthPart`](https://prove2.me/theorems/c43097da-d56f-42d1-8178-075a15d4e395) · Next: [`contDiff_affineOrthPart`](https://prove2.me/theorems/222184b2-bf0f-4088-b7b6-1869ba885db6).
--
--   [Source excerpt, lines 480–483](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/L2/AffineDecomposition.lean#L480-L483) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/L2/AffineDecomposition.lean#L479-L527 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.L2.AffineDecomposition`, declaration `FunctionalInequalities.L2.sub_affineOrthPart_eq`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_L2_AffineDecomposition

open MeasureTheory
open scoped RealInnerProductSpace
variable {n : ℕ}

theorem FunctionalInequalities.L2.sub_affineOrthPart_eq_readable (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) {f g : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f 2 μ)
    (hf0 : ∫ x, f x ∂μ = 0) (hfx : ∀ u, ∫ x, ⟪u, x⟫ * f x ∂μ = 0) (hg : MemLp g 2 μ) :
    f - affineOrthPart μ g = affineOrthPart μ (f - g) := by sorry
