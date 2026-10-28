-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_Computability_PositiveInterpolation_PrescribedTree_datumRoot_conditional_replacement_firstMoment_sat
-- name    : OAI.FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.datumRoot_conditional_replacement_firstMoment_sat
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:22:06.900247+00:00
-- url     : https://prove2.me/theorems/b79825bb-0deb-47e4-bd30-f2146c03069c
-- title:
--   OAI.FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.datumRoot_conditional_replacement_firstMoment_sat (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FixedClauseThreshold.Computability.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Limiting random SAT thresholds, sharp variance and computability (result family 235)*, OpenAI Math Release, September 27, 2026, result family 235, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.datumRoot_conditional_replacement_firstMoment` of [lean/OAI/Probability/SATComputability/InterpolationUpper.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SATComputability/InterpolationUpper.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree`, with `open DilutedSpinGlass DilutedSpinGlass.PrescribedTree DilutedSpinGlass.KernelTower`, `open _root_.MeasureTheory ProbabilityTheory Filter Set`, `open scoped BigOperators NNReal ENNReal Topology`):
--
--   ```lean
--   lemma datumRoot_conditional_replacement_firstMoment_sat (M : Model p) (hM : InterpolationAdmissible M)
--       (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
--       (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
--       (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ d,0 ≤ m d)
--       (hstrict : ∀ d : Fin n,0 < m d.succ) (hroot : m 0=0) (hend : m (Fin.last n)=1)
--       (j : Fin p) (f : FinitePath Ω n → ℝ) (k l : ℕ)
--       (z : RootPath (UpperDatum p N R) k) (w : RootPath (UpperDatum p N R) l)
--       :
--       (∫ a,datumRoot T U V x (fun d => m d.succ) j f (k+1) l (a,z) w ∂upperDatumLaw M Q)+
--         ((p-1:ℕ):ℝ)*datumRoot T U V x (fun d => m d.succ) j f k l z w ≤
--         (p:ℝ)*(∫ a,datumRoot T U V x (fun d => m d.succ) j f k (l+1) z (a,w) ∂upperDatumLaw M Q)-
--         ((p-1:ℕ):ℝ)*(∫ a,edgeRoot Q U x (fun d => m d.succ) a ∂M.disorder.toMeasure)
--   ```
--
--   **Definitions.** The statement is written with `OAI.FixedClauseThreshold.Computability.PositiveInterpolation.InterpolationAdmissible` (definitions bundle `OAIQ067A001` of this split); `OAI.DilutedSpinGlass.Interaction`, `OAI.DilutedSpinGlass.InteractionSample`, `OAI.DilutedSpinGlass.Model` and `OAI.DilutedSpinGlass.Spin` (the published bundle `Def_DilutedSpin`); `OAI.DilutedSpinGlass.FiniteLaw`, `OAI.DilutedSpinGlass.FinitePath`, `OAI.DilutedSpinGlass.KernelTower`, `OAI.DilutedSpinGlass.RootPath`, `OAI.DilutedSpinGlass.PrescribedTree.UpperDatum`, `OAI.DilutedSpinGlass.PrescribedTree.datumRoot`, `OAI.DilutedSpinGlass.PrescribedTree.edgeRoot` and `OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw` (the published bundle `Def_OAIQ041D000`).
--
--   **Used by.** The proof of `OAI.FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.finiteTrial_upper_fixedField_sat` of this split imports it.
-- source:
--   OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 235; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SATComputability/InterpolationUpper.lean (declaration OAI.FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.datumRoot_conditional_replacement_firstMoment)

import Mathlib
import Definitions.Def_DilutedSpin
import Definitions.Def_OAIQ041D000
import Definitions.Def_OAIQ067A001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open DilutedSpinGlass DilutedSpinGlass.PrescribedTree DilutedSpinGlass.KernelTower
open _root_.MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Topology

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma datumRoot_conditional_replacement_firstMoment_sat (M : Model p) (hM : InterpolationAdmissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ d,0 ≤ m d)
    (hstrict : ∀ d : Fin n,0 < m d.succ) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (j : Fin p) (f : FinitePath Ω n → ℝ) (k l : ℕ)
    (z : RootPath (UpperDatum p N R) k) (w : RootPath (UpperDatum p N R) l)
    :
    (∫ a,datumRoot T U V x (fun d => m d.succ) j f (k+1) l (a,z) w ∂upperDatumLaw M Q)+
      ((p-1:ℕ):ℝ)*datumRoot T U V x (fun d => m d.succ) j f k l z w ≤
      (p:ℝ)*(∫ a,datumRoot T U V x (fun d => m d.succ) j f k (l+1) z (a,w) ∂upperDatumLaw M Q)-
      ((p-1:ℕ):ℝ)*(∫ a,edgeRoot Q U x (fun d => m d.succ) a ∂M.disorder.toMeasure) := by
  sorry

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

end

end OAI
end
