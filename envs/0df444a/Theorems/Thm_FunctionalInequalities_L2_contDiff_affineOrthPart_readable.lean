-- Prove2me | Theorems.Thm_FunctionalInequalities_L2_contDiff_affineOrthPart_readable
-- name    : FunctionalInequalities.L2.contDiff_affineOrthPart_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:14.026282+00:00
-- url     : https://prove2.me/theorems/222184b2-bf0f-4088-b7b6-1869ba885db6
-- title:
--   Smoothness and Second Derivative of the Affine-Orthogonal Part
-- statement:
--   This lemma states that subtracting the prescribed affine part preserves $C^2$ regularity and the second derivative.
--
--   Let $n\in\mathbb N$, $E=\mathbb R^n$ (`EuclideanSpace ℝ (Fin n)`), $\mu$ any measure on $E$, and $g:E\to\mathbb R$ a $C^2$ function. For the standard orthonormal basis $(e_j)_{j\in\operatorname{Fin}n}$, define
--   $$
--   \widetilde g(x)=g(x)-\int g\,d\mu-\sum_j\left(\int\langle e_j,y\rangle g(y)\,d\mu(y)\right)\langle e_j,x\rangle
--   $$
--   using `affineOrthPart`. Then
--   $$
--   \widetilde g\in C^2(E),\qquad
--   \forall x\in E,\quad D(D\widetilde g)(x)=D(Dg)(x).
--   $$
--
--   The second derivatives here are the iterated Fréchet derivatives `fderiv`. This result transfers bounded-second-derivative conditions to the affine-subtracted function.
--
--   **Formalization Note** No probability, moment, or integrability assumptions on $\mu$ or $g$ are present. The defining integrals use Lean's total Bochner integral; the lemma does not assert orthogonality under these unrestricted hypotheses.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.L2`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem contDiff_affineOrthPart (μ : Measure (EuclideanSpace ℝ (Fin n)))
--       {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiff ℝ 2 g) :
--       ContDiff ℝ 2 (affineOrthPart μ g) ∧
--         ∀ x, fderiv ℝ (fderiv ℝ (affineOrthPart μ g)) x = fderiv ℝ (fderiv ℝ g) x
--   ```
--
--   **Module navigation**
--
--   Module: [`L2/AffineDecomposition`](https://prove2.me/theorems/78e08949-2f1e-4981-ab20-7428c8af6614).
--
--   Previous: [`sub_affineOrthPart_eq`](https://prove2.me/theorems/816eb15b-7e4e-4f5f-a7bc-08e3b253675d) · Next: [`integral_affineOrthPart_mul_sub`](https://prove2.me/theorems/d02bf2d3-cb86-4723-bceb-c6b16db784b1).
--
--   [Source excerpt, lines 530–533](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/L2/AffineDecomposition.lean#L530-L533) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/L2/AffineDecomposition.lean#L529-L592 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.L2.AffineDecomposition`, declaration `FunctionalInequalities.L2.contDiff_affineOrthPart`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_L2_AffineDecomposition

open MeasureTheory
variable {n : ℕ}

theorem FunctionalInequalities.L2.contDiff_affineOrthPart_readable (μ : Measure (EuclideanSpace ℝ (Fin n)))
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiff ℝ 2 g) :
    ContDiff ℝ 2 (affineOrthPart μ g) ∧
      ∀ x, fderiv ℝ (fderiv ℝ (affineOrthPart μ g)) x = fderiv ℝ (fderiv ℝ g) x := by sorry
