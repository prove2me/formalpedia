-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedPotential_oneJump_shiftedChunk_charge
-- name    : Kyprianou.Ch05.killedPotential_oneJump_shiftedChunk_charge
-- status  : Open
-- author  : @pageman
-- created : 2026-11-26T09:24:06.91819+00:00
-- url     : https://prove2.me/theorems/bf362962-c6e1-584f-aff1-40c7e409fbd3
-- title:
--   One-jump small-time charge into the drift-shifted chunk
-- statement:
--   Let $Y$ be a killed subordinator with finite jump activity, $\Pi(0,\infty)<\infty$, and fix a span $h>0$ and a closed interval $[a,b]$ with $0<a\le b$ avoiding the lattice $h\mathbb{Z}$ entirely. Then for some $\delta>0$ the occupation charge of the drift-shifted chunk $d\,t+[a,b]$ over the time window $(0,\delta]$ is at least quadratic in $\delta$ with coefficient $\Pi([a,b])/3$: $$\exists\,\delta>0,\quad \frac{\delta^2}{3}\,\Pi([a,b])\ \le\ \int_0^\delta P\big(t<\mathrm{death},\ Y_t\in d\,t+[a,b]\big)\,dt.$$ The mechanism is the first jump: a single jump landing in $[a,b]$ at time $s<t$ puts $Y_t$ in the shifted chunk (drift plus the jump size), the one-jump contribution at time $t$ is $\sim t\,\Pi([a,b])$, and integrating over $(0,\delta]$ gives $\sim \delta^2\Pi([a,b])/2$; the constant $1/3$ leaves room for the no-second-jump and survival corrections at small $\delta$. No lattice condition is needed on the landing set, which is why the constant here is the cleaner $1/3$ rather than $1/4$. This is one half of the decomposition of `killedPotential_oneJump_charge_on_chunk`, behind Theorem 5.4(ii) of Kyprianou (2006).
-- source:
--   Kyprianou (2006), first edition, Theorem 5.4, Section 5.1, printed pp. 114-115; decomposition of Kyprianou.Ch05.killedPotential_oneJump_charge_on_chunk (206abf7e-7b7f-474f-9ee0-df9453a347f8).

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

/-- One-jump charge into the drift-shifted chunk. -/
theorem killedPotential_oneJump_shiftedChunk_charge
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
      ∃ δ : Real, 0 < δ ∧ ENNReal.ofReal (δ^2 / 3) * Pi (Set.Icc a b) ≤
        ∫⁻ t in Set.Ioc (0 : Real) δ,
          P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
            Y (Real.toNNReal t) omega ∈ {z : Real | ∃ y ∈ Set.Icc a b, z = d * t + y}} ∂volume)
 := by
  sorry

end Kyprianou.Ch05
