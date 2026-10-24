-- Prove2me | Theorems.Thm_FunctionalInequalities_L2_contDiff_affineOrthPart_408915f
-- name    : FunctionalInequalities.L2.contDiff_affineOrthPart_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:37:30.127434+00:00
-- url     : https://prove2.me/theorems/cf58b182-9c19-48e1-8bc4-54c52a0cffb6
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
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/L2/AffineDecomposition.lean#L529-L592 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.L2.AffineDecomposition`, declaration `FunctionalInequalities.L2.contDiff_affineOrthPart`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_L2_AffineDecomposition
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.L2
end FunctionalInequalities.L2
open FunctionalInequalities FunctionalInequalities.L2
section AffineOrthPart
variable {n : ℕ}

theorem FunctionalInequalities.L2.contDiff_affineOrthPart_408915f (μ : Measure (EuclideanSpace ℝ (Fin n)))
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiff ℝ 2 g) :
    ContDiff ℝ 2 (affineOrthPart μ g) ∧
      ∀ x, fderiv ℝ (fderiv ℝ (affineOrthPart μ g)) x = fderiv ℝ (fderiv ℝ g) x := by sorry
