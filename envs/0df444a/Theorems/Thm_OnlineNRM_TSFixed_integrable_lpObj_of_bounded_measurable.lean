-- Prove2me | Theorems.Thm_OnlineNRM_TSFixed_integrable_lpObj_of_bounded_measurable
-- name    : OnlineNRM.TSFixed.integrable_lpObj_of_bounded_measurable
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T14:54:45.397729+00:00
-- url     : https://prove2.me/theorems/f80365e3-aaef-46f6-894f-355b690fc4a0
-- title:
--   Integrability of a finite LP objective with bounded measurable demand
-- statement:
--   For arbitrary real prices, a finite LP objective is integrable when its demand coordinates are measurable and pointwise interval bounded, and its measurable selector is almost surely nonnegative with total mass at most one.
-- source:
--   Ferreira, Simchi-Levi, Wang, Online Network Revenue Management Using Thompson Sampling, Oper. Res. 66(6), 2018, p. 1594, Theorem 1

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_OnlineNRM_TSFixed_LP

open MeasureTheory OnlineNRM.TSFixed
open scoped BigOperators OnlineNRM.TSFixed

theorem OnlineNRM.TSFixed.integrable_lpObj_of_bounded_measurable
    {N K : ℕ}
    (p : Fin N → Fin K → ℝ) (dbar : Fin N → ℝ)
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (d : Ω → Fin N → Fin K → ℝ)
    (hdmeas : ∀ i k, Measurable (fun ω => d ω i k))
    (hdBound : ∀ ω i k, d ω i k ∈ Set.Icc 0 (dbar i))
    (X : Ω → Fin K → ℝ) (hXmeas : Measurable X)
    (hX : ∀ᵐ ω ∂P, (∀ k, 0 ≤ X ω k) ∧ ∑ k : Fin K, X ω k ≤ 1) :
    Integrable (fun ω => lpObj p (d ω) (X ω)) P := by sorry
