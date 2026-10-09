-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_cusp_kernel_sum_congr
-- name    : OAI.SevenEighths.InverseMoment.cusp_kernel_sum_congr
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:12:34.306878+00:00
-- url     : https://prove2.me/theorems/ad41d05b-89a1-4924-a94b-99a254b360e2
-- title:
--   Equal cusp multiplier sums give equal smoothed kernel sums
-- statement:
--   Let $d_i$ ($i$ in a finite type) and $e_k$ ($k$ in a finite type) be `SourceCuspDatum`s with complex weights $w_i$, $z_k$ such that for every Eisenstein integer $n$, $\sum_iw_i\,\breve e(-\texttt{cuspFrequency}(n)\cdot d_i.\mathrm{point})=\sum_kz_k\,\breve e(-\texttt{cuspFrequency}(n)\cdot e_k.\mathrm{point})$ (with `ShortDraftTrace.breveE`). Then for every smooth $W$ supported in $[lo,hi]$ ($lo>0$) and $X>0$, $\sum_iw_i\,d_i.\texttt{smoothedKernel}\,W\,X=\sum_kz_k\,e_k.\texttt{smoothedKernel}\,W\,X$.
--
--   Lean: `OAI.SevenEighths.InverseMoment.cusp_kernel_sum_congr` in `lean/OAI/NumberTheory/DirichletL/Descent/CuspCongruence.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Definitions.Def_OAIHecke78B021

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff
open MeasureTheory CompletedGauss CubicEisenstein
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem cusp_kernel_sum_congr {ι κ : Type*} [Fintype ι] [Fintype κ]
    (d : ι → SourceCuspDatum) (w : ι → ℂ)
    (e : κ → SourceCuspDatum) (z : κ → ℂ)
    (hmult : ∀ n : Eis,
      (∑ i, w i * ShortDraftTrace.breveE (-cuspFrequency n * (d i).point)) =
        ∑ k, z k * ShortDraftTrace.breveE (-cuspFrequency n * (e k).point))
    (W : ℝ → ℂ) (lo hi : ℝ) (hlo : 0 < lo)
    (hsupp : Function.support W ⊆ Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0 < X) :
    (∑ i, w i * (d i).smoothedKernel W X) = ∑ k, z k * (e k).smoothedKernel W X := by
  sorry

end
end SevenEighths.InverseMoment

end OAI
end
