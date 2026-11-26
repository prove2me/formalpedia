-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedPotential_shiftedChunk_le_offLattice_integral
-- name    : Kyprianou.Ch05.killedPotential_shiftedChunk_le_offLattice_integral
-- status  : Open
-- author  : @pageman
-- created : 2026-11-26T09:24:08.159959+00:00
-- url     : https://prove2.me/theorems/0a54f26c-f71e-5833-a29f-0ad72c04c75e
-- title:
--   Drift-shifted chunk charge is dominated by the off-lattice charge
-- statement:
--   Let $Y$ be a killed subordinator, fix a span $h>0$ and a closed interval $[a,b]$ with $0<a\le b$ avoiding the lattice $h\mathbb{Z}$ entirely. Then for every $\delta$ the occupation charge of the drift-shifted chunk $d\,t+[a,b]$ over $(0,\delta]$ is at most the occupation charge of the off-lattice set: $$\int_0^\delta P\big(t<\mathrm{death},\ Y_t\in d\,t+[a,b]\big)\,dt\ \le\ \int_0^\delta P\big(t<\mathrm{death},\ Y_t\notin h\mathbb{Z}\big)\,dt.$$ The two events differ only where $Y_t$ lies in the lattice $h\mathbb{Z}$; since $[a,b]$ avoids the lattice, the drift can move the shifted chunk onto the lattice only at a countable, hence volume-null, set of times, so the difference integrates to zero. The off-lattice hypothesis on $[a,b]$ is essential: without it the statement is false at $d=0$. No finiteness hypothesis on $\Pi$ is needed. This is one half of the decomposition of `killedPotential_oneJump_charge_on_chunk`, behind Theorem 5.4(ii) of Kyprianou (2006).
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

/-- Drift-shifted chunk charge is dominated by the off-lattice charge. -/
theorem killedPotential_shiftedChunk_le_offLattice_integral
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
  (∀ h : Real, 0 < h → ∀ a b : Real, 0 < a → a ≤ b →
      (∀ z ∈ Set.Icc a b, ∀ n : Int, z ≠ (n : Real) * h) →
      ∀ δ : Real,
        (∫⁻ t in Set.Ioc (0 : Real) δ,
          P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
            Y (Real.toNNReal t) omega ∈ {z : Real | ∃ y ∈ Set.Icc a b, z = d * t + y}} ∂volume) ≤
        ∫⁻ t in Set.Ioc (0 : Real) δ,
          P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
            Y (Real.toNNReal t) omega ∈ {z : Real | ∀ n : Int, z ≠ (n : Real) * h}} ∂volume)
 := by
  sorry

end Kyprianou.Ch05
