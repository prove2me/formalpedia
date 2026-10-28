-- Prove2me | Theorems.Thm_OAI_CoulombBarrier_selected_barriers_limit_positive
-- name    : OAI.CoulombBarrier.selected_barriers_limit_positive
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T05:07:46.715173+00:00
-- url     : https://prove2.me/theorems/db7d8bd1-3e8a-4407-b7d1-023a6b39289e
-- title:
--   OAI.CoulombBarrier.selected_barriers_limit_positive: intermediate lemma from OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoulombAtom.generalized_ionization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Generalized ionization energies for full Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CoulombBarrier.selected_barriers_limit_positive` of [lean/OAI/Analysis/CoulombIonization/RadialBounds/SelectedBarrierLimitBarrier.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/RadialBounds/SelectedBarrierLimitBarrier.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CoulombBarrier`, with `open MeasureTheory Filter`, `open scoped Topology BigOperators ContDiff`, `open MeasureTheory Filter Set Metric`, `open scoped Topology`, `open CoulombAtom CoulombAnalysis`):
--
--   ```lean
--   theorem selected_barriers_limit_positive {ι : Type*} {F : Filter ι} [NeBot F]
--       {s r l Z : ι → ℝ} {a μ p : ι → TFSpace → ℝ} {k B C : ℝ}
--       {F_lim : TFSpace → ℝ}
--       (hs : ∀ i, 0 < s i) (hr : ∀ i, 0 < r i)
--       (hs0 : Tendsto s F (𝓝 0)) (hr0 : Tendsto (fun i => r i/s i) F (𝓝 0))
--       (hl : ∀ i, 0 < l i) (hl0 : Tendsto l F atTop)
--       (hal : ∀ i, 1/(2*l i) ≤ r i/s i) (hk : 0 ≤ k) (hC : 0 ≤ C)
--       (ha : ∀ i, Continuous (a i))
--       (hμm : ∀ i, Measurable (μ i)) (hμi : ∀ i, Integrable (μ i))
--       (hμn : ∀ i x, 0 ≤ μ i x) (hμb : ∀ i, ∃ M ≥ 0, ∀ x, μ i x ≤ M)
--       (hpm : ∀ i, Measurable (p i)) (hpi : ∀ i, Integrable (p i))
--       (hpn : ∀ i x, 0 ≤ p i x) (hpb : ∀ i, ∃ P ≥ 0, ∀ x, p i x ≤ P)
--       (hpSupport : ∀ i x, r i < ‖x‖ → p i x = 0)
--       (hpMass : ∀ i, (∫ x, p i x) ≤ 1)
--       (hweak : ∀ i, WeakNuclearLowerOn univ (Z i)
--         (fun x => nuclearField (Z i) x+a i x)
--         (fun x => innerSource (r i) (μ i) (p i) x+
--           outerCoefficient (r i) x*reaction k (nuclearField (Z i) x+a i x)))
--       (hlower : ∀ i y, r i ≤ ‖y‖ → outerBarrier B (r i) y ≤ nuclearField (Z i) y+a i y)
--       (hupper : ∀ i y, r i ≤ ‖y‖ → nuclearField (Z i) y+a i y ≤ C/‖y‖^4)
--       (hTF : ∀ i x, r i/s i ≤ ‖x‖ → ‖x‖ ≤ l i →
--         tfDilation (s i) (μ i) x ≤
--           k*(max (nuclearField ((s i)^3*Z i) x-tfPotential (tfDilation (s i) (μ i)) x-1) 0)^(3/2:ℝ)+
--             (l i)⁻¹^8/‖x‖^6)
--       (hconv : ∀ S : ℝ, 0 < S → TendstoUniformlyOn
--         (fun i x => nuclearField ((s i)^3*Z i) x-tfPotential (tfDilation (s i) (μ i)) x)
--         F_lim F (sphere (0:TFSpace) S))
--       (hdecay : ∀ ε > 0, ∃ R > 0, ∀ x : TFSpace, R ≤ ‖x‖ → |F_lim x| < ε) :
--       ∀ x : TFSpace, x ≠ 0 → B/‖x‖^4 ≤ F_lim x
--   ```
--
--   **Definitions.** The statement is written with `OAI.CoulombAnalysis.TFSpace`, `OAI.CoulombAnalysis.tfPotential`, `OAI.CoulombAtom.tfDilation` and `OAI.CoulombPDE.Space` (definitions bundle `OAIQ071C000` of this split); `OAI.CoulombBarrier.reaction` (definitions bundle `OAIQ071C002` of this split); `OAI.CoulombBarrier.WeakNuclearLowerOn`, `OAI.CoulombBarrier.innerSource`, `OAI.CoulombBarrier.nuclearField`, `OAI.CoulombBarrier.outerBarrier` and `OAI.CoulombBarrier.outerCoefficient` (definitions bundle `OAIQ071C005` of this split); `OAI.CoulombAtom.Space` (the published bundle `Def_CoulombIonization`).
--
--   **Used by.** The proofs of `OAI.CoulombBarrier.selected_data_profile_subsequence` and `OAI_CoulombBarrier_selected_screened_profile` of this split import it.
-- source:
--   OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-ionization-energies-for-full-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/RadialBounds/SelectedBarrierLimitBarrier.lean (declaration OAI.CoulombBarrier.selected_barriers_limit_positive)

import Mathlib
import Definitions.Def_CoulombIonization
import Definitions.Def_OAIQ071C005

section

attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

theorem selected_barriers_limit_positive {ι : Type*} {F : Filter ι} [NeBot F]
    {s r l Z : ι → ℝ} {a μ p : ι → TFSpace → ℝ} {k B C : ℝ}
    {F_lim : TFSpace → ℝ}
    (hs : ∀ i, 0 < s i) (hr : ∀ i, 0 < r i)
    (hs0 : Tendsto s F (𝓝 0)) (hr0 : Tendsto (fun i => r i/s i) F (𝓝 0))
    (hl : ∀ i, 0 < l i) (hl0 : Tendsto l F atTop)
    (hal : ∀ i, 1/(2*l i) ≤ r i/s i) (hk : 0 ≤ k) (hC : 0 ≤ C)
    (ha : ∀ i, Continuous (a i))
    (hμm : ∀ i, Measurable (μ i)) (hμi : ∀ i, Integrable (μ i))
    (hμn : ∀ i x, 0 ≤ μ i x) (hμb : ∀ i, ∃ M ≥ 0, ∀ x, μ i x ≤ M)
    (hpm : ∀ i, Measurable (p i)) (hpi : ∀ i, Integrable (p i))
    (hpn : ∀ i x, 0 ≤ p i x) (hpb : ∀ i, ∃ P ≥ 0, ∀ x, p i x ≤ P)
    (hpSupport : ∀ i x, r i < ‖x‖ → p i x = 0)
    (hpMass : ∀ i, (∫ x, p i x) ≤ 1)
    (hweak : ∀ i, WeakNuclearLowerOn univ (Z i)
      (fun x => nuclearField (Z i) x+a i x)
      (fun x => innerSource (r i) (μ i) (p i) x+
        outerCoefficient (r i) x*reaction k (nuclearField (Z i) x+a i x)))
    (hlower : ∀ i y, r i ≤ ‖y‖ → outerBarrier B (r i) y ≤ nuclearField (Z i) y+a i y)
    (hupper : ∀ i y, r i ≤ ‖y‖ → nuclearField (Z i) y+a i y ≤ C/‖y‖^4)
    (hTF : ∀ i x, r i/s i ≤ ‖x‖ → ‖x‖ ≤ l i →
      tfDilation (s i) (μ i) x ≤
        k*(max (nuclearField ((s i)^3*Z i) x-tfPotential (tfDilation (s i) (μ i)) x-1) 0)^(3/2:ℝ)+
          (l i)⁻¹^8/‖x‖^6)
    (hconv : ∀ S : ℝ, 0 < S → TendstoUniformlyOn
      (fun i x => nuclearField ((s i)^3*Z i) x-tfPotential (tfDilation (s i) (μ i)) x)
      F_lim F (sphere (0:TFSpace) S))
    (hdecay : ∀ ε > 0, ∃ R > 0, ∀ x : TFSpace, R ≤ ‖x‖ → |F_lim x| < ε) :
    ∀ x : TFSpace, x ≠ 0 → B/‖x‖^4 ≤ F_lim x := by
  sorry

end CoulombBarrier

end

end OAI
end
