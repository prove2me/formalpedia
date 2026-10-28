-- Prove2me | Theorems.Thm_OAI_HardSphere_Bridge_physical_failure_sum
-- name    : OAI.HardSphere.Bridge.physical_failure_sum
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T19:45:18.777852+00:00
-- url     : https://prove2.me/theorems/05f19a9d-15ae-41f3-87d8-dfcdad81fb41
-- title:
--   OAI.HardSphere.Bridge.physical_failure_sum: intermediate lemma from OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HardSphere.condensation_with_mixed`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Ground-state condensation in the dilute hard-sphere gas (result family 267)*, OpenAI Math Release, September 24, 2026, result family 267, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HardSphere.Bridge`, with `open MeasureTheory ProbabilityTheory Set`, `open scoped ENNReal NNReal Topology BigOperators`, `open Wiener GaussianPacking PathCutoff`):
--
--   ```lean
--   lemma physical_failure_sum {L : Length} {N m n : ℕ} (hn : 0<n)
--       (y z : Fin m → Point) (v : Point) (ω : Fin N → ConfigurationPath 1 L)
--       (label : Fin m → Fin N) (J : Finset (Fin N))
--       {t r ε h R C S : ℝ} (w : Time)
--       (hL : 50<L.val) (ht : 0<t) (hr : 0 < r) (hr1 : r≤1) (hε : 0<ε)
--       (hR : 0≤R) (hC : 0≤C) (hh : 0<h) (hw : (w:ℝ)=h/t)
--       (hsepY : ∀i j,i≠j → ε^2≤ square (y i-y j))
--       (hsepZ : ∀i j,i≠j → ε^2≤ square (z i-z j))
--       (hreg : ∀j∈J,Regular (n+n) r R C (prefixTime midpointTime w) S (ω j))
--       (hsmall : r*R≤1) (hτr : t/(n:ℝ) ≤ r^2) (hnscale : (n:ℝ)*r^2≤2*t)
--       (hwindow : 2*(t/(n:ℝ))≤h) (hlarge : 8*t≤(n:ℝ)*h) (hdrift : 2*13/(n:ℝ) ≤ r)
--       {B : Set Point} (hB : MeasurableSet B) (hBvol : volume B≤1)
--       (hBv : ∀u∈B,‖u-v‖≤3)
--       (hBY : ∀i u,u∈B → ‖u-y i‖≤13) (hBZ : ∀i u,u∈B → ‖u-z i‖≤13)
--       (hy : ∀j∈J,∀i,j≠label i → r+2*S<torusDistance L (projectPoint L (y i)) (ω j 0 0))
--       (hz : ∀j∈J,∀i,j≠label i → r+2*S<torusDistance L (projectPoint L (z i)) (ω j 1 0))
--       (hfar : ∀j,j∉J → ∀s,12<torusDistance L (ω j s 0) (projectPoint L v))
--       (δ : ℝ≥0∞)
--       (hcut : ∀i u,u∈B → trialKernel t (y i) (z i) u {f | ¬TrialCutoff L n r R C w S v f}≤δ) :
--       (∑i,∫⁻u in B,trialKernel t (y i) (z i) u (SuccessExcept n r R C S w v ω (label i))ᶜ)≤
--         (m:ℝ≥0∞)*δ+(J.card:ℝ≥0∞)*(2*ENNReal.ofReal
--           (hitConstant*(8*C*t*r*(ε⁻¹^3+(m:ℝ))+8*r*(1+R)^3/Real.sqrt (h/2))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.HardSphere.ConfigurationPath`, `OAI.HardSphere.Bridge.SuccessExcept`, `OAI.HardSphere.Bridge.TrialCutoff`, `OAI.HardSphere.Bridge.hitConstant`, `OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint`, `OAI.HardSphere.Bridge.midpointTime`, `OAI.HardSphere.Bridge.projectPoint`, `OAI.HardSphere.Bridge.trialKernel`, `OAI.HardSphere.GaussianPacking.Point`, `OAI.HardSphere.GaussianPacking.square`, `OAI.HardSphere.PathCutoff.Regular`, `OAI.HardSphere.Wiener.Time` and `OAI.HardSphere.Wiener.prefixTime` (definitions bundle `OAIQ054H000` of this split); `OAI.HardSphere.Configuration`, `OAI.HardSphere.Length`, `OAI.HardSphere.Torus` and `OAI.HardSphere.torusDistance` (the published bundle `Def_HardSphere`).
--
--   **Used by.** The proof of `OAI.HardSphere.Groups.canonical_supply_counts` of this split imports it.
-- source:
--   OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 267; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Ground-state-condensation-in-the-dilute-hard-sphere-gas-September-24-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_HardSphere
import Definitions.Def_OAIQ054H000

section

attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff
attribute [local irreducible] torusDistance
attribute [local instance] Classical.propDecidable

lemma physical_failure_sum {L : Length} {N m n : ℕ} (hn : 0<n)
    (y z : Fin m → Point) (v : Point) (ω : Fin N → ConfigurationPath 1 L)
    (label : Fin m → Fin N) (J : Finset (Fin N))
    {t r ε h R C S : ℝ} (w : Time)
    (hL : 50<L.val) (ht : 0<t) (hr : 0 < r) (hr1 : r≤1) (hε : 0<ε)
    (hR : 0≤R) (hC : 0≤C) (hh : 0<h) (hw : (w:ℝ)=h/t)
    (hsepY : ∀i j,i≠j → ε^2≤ square (y i-y j))
    (hsepZ : ∀i j,i≠j → ε^2≤ square (z i-z j))
    (hreg : ∀j∈J,Regular (n+n) r R C (prefixTime midpointTime w) S (ω j))
    (hsmall : r*R≤1) (hτr : t/(n:ℝ) ≤ r^2) (hnscale : (n:ℝ)*r^2≤2*t)
    (hwindow : 2*(t/(n:ℝ))≤h) (hlarge : 8*t≤(n:ℝ)*h) (hdrift : 2*13/(n:ℝ) ≤ r)
    {B : Set Point} (hB : MeasurableSet B) (hBvol : volume B≤1)
    (hBv : ∀u∈B,‖u-v‖≤3)
    (hBY : ∀i u,u∈B → ‖u-y i‖≤13) (hBZ : ∀i u,u∈B → ‖u-z i‖≤13)
    (hy : ∀j∈J,∀i,j≠label i → r+2*S<torusDistance L (projectPoint L (y i)) (ω j 0 0))
    (hz : ∀j∈J,∀i,j≠label i → r+2*S<torusDistance L (projectPoint L (z i)) (ω j 1 0))
    (hfar : ∀j,j∉J → ∀s,12<torusDistance L (ω j s 0) (projectPoint L v))
    (δ : ℝ≥0∞)
    (hcut : ∀i u,u∈B → trialKernel t (y i) (z i) u {f | ¬TrialCutoff L n r R C w S v f}≤δ) :
    (∑i,∫⁻u in B,trialKernel t (y i) (z i) u (SuccessExcept n r R C S w v ω (label i))ᶜ)≤
      (m:ℝ≥0∞)*δ+(J.card:ℝ≥0∞)*(2*ENNReal.ofReal
        (hitConstant*(8*C*t*r*(ε⁻¹^3+(m:ℝ))+8*r*(1+R)^3/Real.sqrt (h/2)))) := by
  sorry

end HardSphere.Bridge

end
end

end

end OAI
end
