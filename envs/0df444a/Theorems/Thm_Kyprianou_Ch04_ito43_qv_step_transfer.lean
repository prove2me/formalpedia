-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_qv_step_transfer
-- name    : Kyprianou.Ch04.ito43_qv_step_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T22:13:54.970645+00:00
-- url     : https://prove2.me/theorems/de548fd0-30e6-5de0-a4be-2b394fdf98d4
-- title:
--   Finite step combinations inherit uniform convergence
-- statement:
--   Each threshold error vanishes uniformly. For the finite collection choose a common late index, and bound the absolute sum by the sum of absolute coefficients times a common small tolerance.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology

open Set

theorem Kyprianou.Ch04.ito43_qv_step_transfer  {Omega : Type} [MeasurableSpace Omega]
    (X Xleft : NNReal → Omega → ℝ) (w : Omega)
    (hc : IsCadlag (fun t => X t w))
    (hl : ∀ t : NNReal, 0 < t →
      Tendsto (fun s => X s w) (nhdsWithin t (Set.Iio t)) (nhds (Xleft t w)))
    (σ : ℝ) (hσ : 0 ≤ σ)
    (g : ℝ × ℝ → ℝ)
    (hg : ContinuousOn g (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set ℝ)))
    (T : NNReal)
    (hs : Summable (fun s : Set.Ioc (0:NNReal) (T+1) => (X s w-Xleft s w)^2))
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) :
    let A : ℕ → NNReal → ℝ := fun n t =>
      let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      σ *
      (∫ s in Set.Icc (0 : ℝ) (t : ℝ), (1 : ℝ) ∂volume) + (∫ z in Set.prod (Set.Icc (0 : ℝ) (t : ℝ)) (Set.univ : Set ℝ),
      z.2^2 / 2 ∂(pathJumpMeasure X Xleft w)) - (∑ k ∈ Finset.range n,
      (X (v (k+1)) w - X (v k) w)^2 / 2)
    let F : NNReal → ℝ := fun t =>
      σ * (∫ s in Icc (0:ℝ) (t:ℝ), (1:ℝ) ∂volume) +
      ∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ), z.2^2/2 ∂(pathJumpMeasure X Xleft w)
    let D : ℕ → NNReal → NNReal → ℝ := fun n b t =>
      let u : ℕ → NNReal := fun k => T*(k:NNReal)/(n:NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      F t-F (min t b) -
        ∑ k ∈ Finset.range n, (if b ≤ u k then (1:ℝ) else 0) *
          (X (v (k+1)) w-X (v k) w)^2/2
    let E : ℕ → (ℕ → NNReal) → (ℕ → ℝ) → ℕ → NNReal → ℝ :=
      fun m b c n t => ∑ i ∈ Finset.range m, c i * D n (b i) t
    (∀ e : ℝ, 0 < e → ∀ᶠ n in atTop, ∀ t ≤ T, |A (N n) t| < e) →
      ∀ (m : ℕ) (b : ℕ → NNReal) (c : ℕ → ℝ) (e : ℝ), 0 < e →
        ∀ᶠ n in atTop, ∀ t ≤ T, |E m b c (N n) t| < e := by sorry
