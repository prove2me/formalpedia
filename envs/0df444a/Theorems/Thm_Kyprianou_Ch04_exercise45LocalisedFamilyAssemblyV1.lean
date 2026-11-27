-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45LocalisedFamilyAssemblyV1
-- name    : Kyprianou.Ch04.exercise45LocalisedFamilyAssemblyV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:30:15.293925+00:00
-- url     : https://prove2.me/theorems/ca6f5c77-1d70-513a-b7a6-9a713068a9b5
-- title:
--   Glue compatible bounded physical stochastic integrals into a local witness
-- statement:
--   Agreement of the test weights and drift/large-jump terms through each local clock, and the Ito residual strictly before it, implies stopped martingale consistency, global UCP and global residual equality.
-- source:
--   Kyprianou (2006), Exercise 4.5(iv), localisation.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
open MeasureTheory Filter Set
open scoped NNReal ENNReal Classical
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem exercise45LocalisedFamilyAssemblyV1 :
∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X H D R : NNReal → Ω → ℝ)
    (Hn Dn Rn Mn : ℕ → NNReal → Ω → ℝ) (τ : ℕ → Ω → NNReal)
    (hMeas : ∀ n T, MeasurableSet {w | τ n w ≤ T})
    (hMono : ∀ w, Monotone (fun n => τ n w))
    (hCof : ∀ᵐ w ∂P, Tendsto (fun n => (τ n w : WithTop NNReal)) atTop (nhds ⊤))
    (hPrefix : ∀ᵐ w ∂P, ∀ n t, t ≤ τ n w → Hn n t w = H t w ∧ Dn n t w = D t w)
    (hResidual : ∀ᵐ w ∂P, ∀ n t, t < τ n w → Rn n t w = R t w)
    (hUCP : ∀ n, IsStochasticIntegralInProbabilityV2 P X (Hn n) (fun t w => Dn n t w + Mn n t w))
    (hIto : ∀ n, ∀ᵐ w ∂P, ∀ t, Rn n t w = Dn n t w + Mn n t w),
    let M : NNReal → Ω → ℝ := fun t w =>
      if h : ∃ k : ℕ, t ≤ τ k w then Mn (Nat.find h) t w else 0
    (∀ᵐ w ∂P, ∀ n m : ℕ, n ≤ m → ∀ t,
      Mn m (min t (τ n w)) w = Mn n (min t (τ n w)) w) ∧
    IsStochasticIntegralInProbabilityV2 P X H (fun t w => D t w + M t w) ∧
    (∀ᵐ w ∂P, ∀ t, R t w = D t w + M t w)
 := by
  sorry
end Kyprianou.Ch04
