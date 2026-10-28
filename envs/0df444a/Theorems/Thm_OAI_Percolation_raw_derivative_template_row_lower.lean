-- Prove2me | Theorems.Thm_OAI_Percolation_raw_derivative_template_row_lower
-- name    : OAI.Percolation.raw_derivative_template_row_lower
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T00:52:35.843805+00:00
-- url     : https://prove2.me/theorems/89fd4d06-33d8-4f50-b9b1-a531b0e2e076
-- title:
--   OAI.Percolation.raw_derivative_template_row_lower: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.arbitrary_cayley`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Percolation.raw_derivative_template_row_lower` of [lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Deformation/AveragedDecrease.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Deformation/AveragedDecrease.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Percolation`, with `open MeasureTheory ProbabilityTheory`, `open scoped ENNReal NNReal`, `open MeasureTheory`):
--
--   ```lean
--   theorem raw_derivative_template_row_lower (G : BondGraph V E) (hG : Function.Injective G)
--       (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
--       (d : ℕ) (hd : ∀ x, degree G x ≤ d)
--       (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (hpcrit : 0 < (pc G:ℝ))
--       (p : unitInterval) (hp : p < pc G) (hpnear : (pc G:ℝ)/2 ≤ (p:ℝ))
--       (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T)
--       (k : ℕ) (w : RawCorridor G k)
--       (c : ℝ) (hc : (∑ e ∈ (w.retained_finite hG).toFinset, ∑' r : RawCorridor G k,
--           if e ∈ r.retained then r.weight P p else 0) ≤ c)
--       (t : ℝ) (ht : 0 ≤ t) :
--       Real.exp (-t*c) * (w.probability P *
--         (retainedSusceptibilityProduct G P p t w -
--           (1+2*(d:ℝ)/(pc G:ℝ))*(maxSusceptibility G p)^2*(matrixCoeff (T^3) w.base w.endpoint).re)) ≤
--         ∑' xy : V × V, corridorDerivativeContribution G P p t w xy.1 xy.2
--   ```
--
--   **Definitions.** The statement is written with `OAI.Percolation.LocallyFinite`, `OAI.Percolation.QuasiTransitive`, `OAI.Percolation.RawCorridor`, `OAI.Percolation.matrixCoeff`, `OAI.Percolation.RawCorridor.base`, `OAI.Percolation.RawCorridor.endpoint`, `OAI.Percolation.RawCorridor.probability`, `OAI.Percolation.RawCorridor.retained`, `OAI.Percolation.RawCorridor.retained_finite` and `OAI.Percolation.RawCorridor.weight` (definitions bundle `OAIQ040C000` of this split); `OAI.Percolation.corridorDerivativeContribution`, `OAI.Percolation.degree`, `OAI.Percolation.maxSusceptibility` and `OAI.Percolation.retainedSusceptibilityProduct` (definitions bundle `OAIQ040C002` of this split); `OAI.Percolation.BondGraph`, `OAI.Percolation.HasKernel`, `OAI.Percolation.Hilbert` and `OAI.Percolation.pc` (the published bundle `Def_CayleyPercolation`).
--
--   **Used by.** The proof of `OAI.Percolation.exists_uniform_averaged_decrease` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Deformation/AveragedDecrease.lean (declaration OAI.Percolation.raw_derivative_template_row_lower)

import Mathlib
import Definitions.Def_CayleyPercolation
import Definitions.Def_OAIQ040C002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section AveragedCalibratedDecrease
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]
variable {ι : Type*} [Fintype ι]

theorem raw_derivative_template_row_lower (G : BondGraph V E) (hG : Function.Injective G)
    (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (hpcrit : 0 < (pc G:ℝ))
    (p : unitInterval) (hp : p < pc G) (hpnear : (pc G:ℝ)/2 ≤ (p:ℝ))
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T)
    (k : ℕ) (w : RawCorridor G k)
    (c : ℝ) (hc : (∑ e ∈ (w.retained_finite hG).toFinset, ∑' r : RawCorridor G k,
        if e ∈ r.retained then r.weight P p else 0) ≤ c)
    (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-t*c) * (w.probability P *
      (retainedSusceptibilityProduct G P p t w -
        (1+2*(d:ℝ)/(pc G:ℝ))*(maxSusceptibility G p)^2*(matrixCoeff (T^3) w.base w.endpoint).re)) ≤
      ∑' xy : V × V, corridorDerivativeContribution G P p t w xy.1 xy.2 := by
  sorry

end AveragedCalibratedDecrease
end Percolation

end OAI
end
