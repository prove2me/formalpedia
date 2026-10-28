-- Prove2me | Theorems.Thm_OAI_Percolation_raw_derivative_template_row_lower_bs
-- name    : OAI.Percolation.raw_derivative_template_row_lower_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T15:42:08.173327+00:00
-- url     : https://prove2.me/theorems/5a0503aa-75b2-4306-bcd4-e272ad7073e5
-- title:
--   OAI.Percolation.raw_derivative_template_row_lower_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Percolation.raw_derivative_template_row_lower` of [lean/OAI/Probability/UnimodularPercolation/Deformation/AveragedDecrease.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/Deformation/AveragedDecrease.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Percolation`, with `open MeasureTheory ProbabilityTheory`, `open scoped ENNReal NNReal`, `open MeasureTheory`):
--
--   ```lean
--   theorem raw_derivative_template_row_lower_bs (G : BondGraph V E) (hG : Function.Injective G)
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
--   **Definitions.** The statement is written with `OAI.Percolation.matrixCoeff` (definitions bundle `OAIQ078B001` of this split); `OAI.Percolation.RawCorridor`, `OAI.Percolation.corridorDerivativeContribution`, `OAI.Percolation.degree`, `OAI.Percolation.maxSusceptibility`, `OAI.Percolation.retainedSusceptibilityProduct`, `OAI.Percolation.RawCorridor.base`, `OAI.Percolation.RawCorridor.endpoint`, `OAI.Percolation.RawCorridor.probability`, `OAI.Percolation.RawCorridor.retained`, `OAI.Percolation.RawCorridor.retained_finite` and `OAI.Percolation.RawCorridor.weight` (definitions bundle `OAIQ078B002` of this split); `OAI.Percolation.BondGraph`, `OAI.Percolation.HasKernel`, `OAI.Percolation.Hilbert`, `OAI.Percolation.LocallyFinite`, `OAI.Percolation.QuasiTransitive` and `OAI.Percolation.pc` (the published bundle `Def_BenjaminiSchramm`).
--
--   **Used by.** The proof of `OAI.Percolation.exists_uniform_averaged_decrease_bs` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/Deformation/AveragedDecrease.lean (declaration OAI.Percolation.raw_derivative_template_row_lower)

import Mathlib
import Definitions.Def_BenjaminiSchramm
import Definitions.Def_OAIQ078B002

section

attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
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

theorem raw_derivative_template_row_lower_bs (G : BondGraph V E) (hG : Function.Injective G)
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
