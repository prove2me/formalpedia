-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedPotential_oneJump_charge_on_chunk
-- name    : Kyprianou.Ch05.killedPotential_oneJump_charge_on_chunk
-- status  : Open
-- author  : @pageman
-- created : 2026-11-26T04:13:21.889804+00:00
-- url     : https://prove2.me/theorems/206abf7e-7b7f-474f-9ee0-df9453a347f8
-- title:
--   One-jump small-time charge localized to an off-lattice interval chunk
-- statement:
--   Let $Y$ be a killed subordinator with finite jump activity, $\Pi(0,\infty)<\infty$, and fix a span $h>0$ and a closed interval $[a,b]$ with $0<a\le b$ that avoids the lattice $h\mathbb Z$ entirely. Then for some $\delta>0$ the discounted occupation charge of the off-lattice set over the time window $(0,\delta]$ is at least quadratic in $\delta$ with coefficient $\Pi([a,b])/4$:
--
--   $$\exists\,\delta>0,\quad \frac{\delta^2}{4}\,\Pi([a,b])\ \le\ \int_0^\delta P\big(t<\mathrm{death},\ Y_t\notin h\mathbb Z\big)\,dt.$$
--
--   The mechanism is the first jump: a single jump landing in $[a,b]$ at time $s<t$ puts $Y_t$ off the lattice (the drift can move the position onto the lattice only at a countable, hence null, set of times), the one-jump contribution at time $t$ is $\sim t\,\Pi([a,b])$, and integrating over $(0,\delta]$ gives $\sim \delta^2\Pi([a,b])/2$; the constant $1/4$ leaves room for the no-second-jump and survival corrections at small $\delta$. This is the localized analytic core of `killedPotential_firstJump_smallTime_charge`, behind Theorem 5.4(ii) of Kyprianou (2006).
--
--   **Formalization Note.** Same binder block as `killedPotential_firstJump_smallTime_charge`; no hypothesis on $\Pi([a,b])$ is needed since the inequality is trivial when it vanishes.
-- source:
--   Kyprianou (2006), first edition, Theorem 5.4, Section 5.1, printed pp. 114-115; decomposition of Kyprianou.Ch05.killedPotential_firstJump_smallTime_charge (11cd9fb9-9a47-45c2-9335-81edebd6bc1e).

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

/-- First-jump asymptotics localized to an off-lattice chunk give a quadratic small-time occupation charge. -/
theorem killedPotential_oneJump_charge_on_chunk
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
      ∃ δ : Real, 0 < δ ∧ ENNReal.ofReal (δ^2 / 4) * Pi (Set.Icc a b) ≤
        ∫⁻ t in Set.Ioc (0 : Real) δ,
          P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
            Y (Real.toNNReal t) omega ∈ {z : Real | ∀ n : Int, z ≠ (n : Real) * h}} ∂volume)
 := by
  sorry

end Kyprianou.Ch05
