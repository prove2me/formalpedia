-- Prove2me | Theorems.Thm_OAI_SKGap_realTruncatedK_first_loop_s2
-- name    : OAI.SKGap.realTruncatedK_first_loop_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:48:36.07993+00:00
-- url     : https://prove2.me/theorems/3e5f3d25-2b38-4664-876b-c614a16d9709
-- title:
--   OAI.SKGap.realTruncatedK_first_loop_s2: intermediate lemma from OpenAI, Critical mixing in the Sherrington-Kirkpatrick model (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalSK.critical_mixing_bounds`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Critical mixing in the Sherrington-Kirkpatrick model (result family 227)*, OpenAI Math Release, September 25, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGap`, with `open MeasureTheory ProbabilityTheory InformationTheory Real Set`, `open scoped NNReal ENNReal`, `open Filter`, `open scoped Topology`, `open Matrix Real`, `open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal`, `open Matrix Real`, `open scoped BigOperators Matrix.Norms.Frobenius NNReal`, `open MeasureTheory ProbabilityTheory Real Set Filter`, `open MeasureTheory.Measure`, `open scoped ENNReal NNReal MeasureTheory Topology`, `open MeasureTheory`, `open MeasureTheory Set NormedSpace`, `open scoped Topology`, `open Matrix Real`, `open scoped BigOperators Matrix.Norms.Frobenius`, `open Set Real`, `open scoped Topology`, `open Matrix Set Filter`, `open scoped Topology Matrix.Norms.Frobenius`, `open Matrix NormedSpace ContinuousLinearMap`, `open scoped Matrix.Norms.Frobenius`, `open Matrix`, `open Matrix Real MeasureTheory ProbabilityTheory`, `open SKGap.RealComplex`, `open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap`):
--
--   ```lean
--   theorem realTruncatedK_first_loop_s2 (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0 < lo)
--       (hf : ∀ x ∈ Set.Icc lo hi, f x = (x : ℂ)⁻¹)
--       {R r : ℝ} (hR : 0 ≤ R) (hr : 0 ≤ r) (D C : Matrix ι ι ℝ)
--       (hD : Dᵀ = D) (hC : Cᵀ = C) (i : ι) :
--       let K := realTruncatedK f R hR D C
--       let c := ComplexMatrix.kBound f R (liftMatrix D) (liftMatrix C)
--       let L := Real.toNNReal (ComplexMatrix.kLip f R (liftMatrix D) (liftMatrix C))
--       let Lπ : ℝ≥0 := L*(⟨sqrt (2*r),sqrt_nonneg _⟩ *
--         (Fintype.card (MatrixCoordinates ι) : ℝ≥0) ^ (1/(2:ℝ≥0∞)).toReal)
--       let T : ℝ≥0 := (⟨sqrt (Fintype.card ι)*opNorm (D*D),
--         mul_nonneg (sqrt_nonneg _) (norm_nonneg _)⟩*L)*⟨sqrt (2*r),sqrt_nonneg _⟩+1
--       let μ := Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)
--       |(∫ g, (goeMatrix r g*K (goeMatrix r g)) i i ∂μ)-
--         r*(∫ g, Matrix.trace (K (goeMatrix r g)*(D*D)) ∂μ)*(∫ g, K (goeMatrix r g) i i ∂μ)| ≤
--         (Fintype.card ι:ℝ)*(sqrt (2*r)*(Lπ:ℝ)+r*(2*c*opNorm (D*D)*c))*
--           μ.real (truncationGoodSet r R lo hi D C)ᶜ+
--           r*(c*((2*Real.exp (π^2/8))*(T:ℝ))+c*opNorm (D*D)*c)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.MatrixCoordinates`, `OAI.SKGap.goeMatrix`, `OAI.SKGap.opNorm`, `OAI.SKGap.truncationGoodSet`, `OAI.SKGap.ComplexMatrix.kBound`, `OAI.SKGap.ComplexMatrix.kLip`, `OAI.SKGap.RealComplex.liftMatrix` and `OAI.SKGap.RealComplex.realTruncatedK` (definitions bundle `OAIQ072A000` of this split).
--
--   **Used by.** No other item of this split imports it.
-- source:
--   OpenAI, Critical mixing in the Sherrington-Kirkpatrick model (result family 227), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-mixing-in-the-Sherrington-Kirkpatrick-model-September-25-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ072A000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory
open SKGap.RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem realTruncatedK_first_loop_s2 (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0 < lo)
    (hf : ∀ x ∈ Set.Icc lo hi, f x = (x : ℂ)⁻¹)
    {R r : ℝ} (hR : 0 ≤ R) (hr : 0 ≤ r) (D C : Matrix ι ι ℝ)
    (hD : Dᵀ = D) (hC : Cᵀ = C) (i : ι) :
    let K := realTruncatedK f R hR D C
    let c := ComplexMatrix.kBound f R (liftMatrix D) (liftMatrix C)
    let L := Real.toNNReal (ComplexMatrix.kLip f R (liftMatrix D) (liftMatrix C))
    let Lπ : ℝ≥0 := L*(⟨sqrt (2*r),sqrt_nonneg _⟩ *
      (Fintype.card (MatrixCoordinates ι) : ℝ≥0) ^ (1/(2:ℝ≥0∞)).toReal)
    let T : ℝ≥0 := (⟨sqrt (Fintype.card ι)*opNorm (D*D),
      mul_nonneg (sqrt_nonneg _) (norm_nonneg _)⟩*L)*⟨sqrt (2*r),sqrt_nonneg _⟩+1
    let μ := Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)
    |(∫ g, (goeMatrix r g*K (goeMatrix r g)) i i ∂μ)-
      r*(∫ g, Matrix.trace (K (goeMatrix r g)*(D*D)) ∂μ)*(∫ g, K (goeMatrix r g) i i ∂μ)| ≤
      (Fintype.card ι:ℝ)*(sqrt (2*r)*(Lπ:ℝ)+r*(2*c*opNorm (D*D)*c))*
        μ.real (truncationGoodSet r R lo hi D C)ᶜ+
        r*(c*((2*Real.exp (π^2/8))*(T:ℝ))+c*opNorm (D*D)*c) := by
  sorry

end SKGap

end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end
