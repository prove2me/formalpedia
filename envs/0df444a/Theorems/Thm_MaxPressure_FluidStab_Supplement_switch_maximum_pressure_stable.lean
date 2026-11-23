-- Prove2me | Theorems.Thm_MaxPressure_FluidStab_Supplement_switch_maximum_pressure_stable
-- name    : MaxPressure.FluidStab.Supplement.switch_maximum_pressure_stable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T08:24:43.743969+00:00
-- url     : https://prove2.me/theorems/1bc9a697-77ea-47da-8627-45290bc36488
-- title:
--   Theorem 10 (corrected: finite input rates; local slot units) — network switch stability
-- statement:
--   Consider any finite network of input-queued switches with per-flow queues and fixed finite routes, one visit per port pair on each route. Let switch $s$ have local slot duration $d_s>0$ in common wall time, with arbitrary phases. Let the input requirement of flow $c$ have mean $m_c>0$ and satisfy (3), and put $\alpha_c=1/m_c$. Assume the local-unit traffic bounds
--
--   $$d_{s(u)}\sum_{c,v}\alpha_c H_{c,(u,v)}\le1,\qquad d_{s(v)}\sum_{c,u}\alpha_c H_{c,(u,v)}\le1.$$
--
--   Under any nonpreemptive, non-processor-splitting maximum-pressure matching policy at each switch's slot boundaries, every per-flow queue is pathwise stable for every legal initial state:
--
--   $$\forall s_0\text{ legal},\quad\Pr\!\left(\forall i,\ \lim_{t\to\infty}Z_i^{s_0}(t)/t=0\right)=1.$$
--
--   The queue index includes both flow and route position; flows may share pairs and revisit a switch through another pair. Arbitrary maximizer ties and unsynchronized switches are included. Routes and transmission times are deterministic; no EAA, reversed-Leontief property, service moment law or Assumption 3 is added. With all $d_s=1$, the traffic bounds are exactly (33)–(34).
--
--   **Formalization Note** The unequal-duration extension requires converting offered load into local slot units. TIME_UNITS.md records the conversion and source anchors. A duration-two switch with wall-time arrival rate $3/4$ overloads its capacity, but lies outside the printed model with service means one; it is not a refutation of Theorem 10.
--
--   Differences from the source:
--
--   - correction: The page allows nonnegative input mean requirements but defines arrival rates by their inverses. → Every flow has a finite positive input mean.; reason: This is the published finite-rate interpretation; zero-mean infinite-rate inputs are excluded rather than assigned inverse zero.
--   - reading: The text allows different local time units and then normalizes every service mean to one in the stochastic-processing-network model. → Port loads in common wall time include the local slot duration; setting every duration to one recovers the printed bounds.; reason: Arrival counts per local slot equal the common-wall-time rate times the slot duration. The duration-two overload example lies outside the normalized source model; no source instance is excluded.
--   - encoding: A finite network of switches with per-flow FIFO queues, arbitrary initial states, and local slots. → Finite dependent route positions, constructed input/service network, immutable episode ownership, arbitrary slot phases and compatible initial residuals.; reason: This covers shared pairs, repeated switches on distinct pairs, all network sizes and initial transmissions without assuming the derived EAA or fluid equations.
--   - generalization: Arbitrary randomized maximizing ties use the past. → All realized matching choices, including anticipating maximizing ties, are quantified over.; reason: Pathwise arguments do not require independence or a restriction on how a maximizing tie is selected.
-- source:
--   Dai & Lin, Maximum pressure policies in stochastic processing networks, Oper. Res. 53(2) (2005), p. 211, Theorem 10; https://doi.org/10.1287/opre.1040.0170

import Mathlib
import Definitions.Def_MaxPressure_FluidStab_Supplement_Switches

namespace MaxPressure.FluidStab.Supplement

open MeasureTheory Filter Topology

theorem switch_maximum_pressure_stable
    {S U V C : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (D : SwitchData S U V C) (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (η : Fin C → ℕ → Ω → ℝ)
    (p : Policy (queueCount D) (C + queueCount D) Ω)
    (hD : D.Valid) (hinput : SwitchInputs D η Pr) (htraffic : SwitchTraffic D)
    (hlegal : ∀ s, SwitchInitial D s →
      (∀ t i, 0 ≤ t → Measurable (fun ω => (p s ω).Z t i)) ∧
      ∀ᵐ ω ∂Pr, LegalHistory (switchNetwork D) (switchPrimitives D η) s ω (p s ω) true)
    (hMP : ∀ s, SwitchInitial D s →
      ∀ᵐ ω ∂Pr, SwitchMaximumPressure D s (p s ω)) :
    SwitchStable D Pr p := by sorry

end MaxPressure.FluidStab.Supplement
