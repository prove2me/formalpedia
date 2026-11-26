-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedPotential_oneJump_shiftedChunk_pointwise
-- name    : Kyprianou.Ch05.killedPotential_oneJump_shiftedChunk_pointwise
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-26T11:26:00.303996+00:00
-- url     : https://prove2.me/theorems/07ce02b1-421d-4974-8fb7-65b4393c5cd1
-- title:
--   Pointwise one-jump charge into the drift-shifted chunk
-- statement:
--   For a killed subordinator with Laplace triplet $(\eta, d, \Pi)$ and $\Pi((0,\infty))$ finite, given $h>0$ and an interval $[a,b]$ with $0<a\le b$ lying entirely off the lattice $h\mathbb{Z}$, there exists $\delta>0$ such that for every $t\in(0,\delta)$, the probability that the process is still alive at time $t$ and its position lies in the drift-shifted chunk $\{d t + y : y\in[a,b]\}$ is at least $\frac{2t}{3}\,\Pi([a,b])$. This is the pointwise small-time one-jump asymptotics: exactly one jump into the chunk occurs with probability $\sim t\,\Pi([a,b])$, while the no-second-jump and survival factors tend to $1$, which yields the constant $2/3$ for all sufficiently small $t$.
-- source:
--   Kyprianou, Introductory Lectures on Fluctuations of Levy Processes with Applications (2006), Chapter 5, Theorem 5.4 proof (first-jump asymptotics). Decomposition child of Kyprianou.Ch05.killedPotential_oneJump_shiftedChunk_charge.

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Pointwise small-time lower bound for the one-jump charge into the drift-shifted chunk. -/
theorem killedPotential_oneJump_shiftedChunk_pointwise
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : IsKilledSubordinator P Y death eta)
    (hTriplet : IsKilledLaplaceTriplet eta d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * (Phi theta - eta)))
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U) :
  (Pi (Set.Ioi (0 : Real)) < ⊤ →
    ∀ h : Real, 0 < h → ∀ a b : Real, 0 < a → a ≤ b →
      (∀ z ∈ Set.Icc a b, ∀ n : Int, z ≠ (n : Real) * h) →
      ∃ δ : Real, 0 < δ ∧ ∀ t ∈ Set.Ioc (0 : Real) δ,
        ENNReal.ofReal (2 * t / 3) * Pi (Set.Icc a b) ≤
          P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
            Y (Real.toNNReal t) omega ∈ {z : Real | ∃ y ∈ Set.Icc a b, z = d * t + y}})
 := by
  sorry

end Kyprianou.Ch05
