-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedPotential_shiftedChunk_lattice_integral_eq_zero
-- name    : Kyprianou.Ch05.killedPotential_shiftedChunk_lattice_integral_eq_zero
-- status  : Open
-- author  : @pageman
-- created : 2026-11-26T11:25:49.113214+00:00
-- url     : https://prove2.me/theorems/44dc1c7b-0da5-454a-87db-c1dbe32398e2
-- title:
--   Shifted chunk meets the lattice only on a null set of times
-- statement:
--   Let $Y$ be a killed subordinator with killing rate $\eta \ge 0$, drift $d \ge 0$ and Lévy measure $\Pi$ on $(0,\infty)$, and fix a spacing $h > 0$ and a compact interval $[a,b]$ with $0 < a \le b$ that avoids the lattice $h\mathbb{Z}$ entirely. For a time horizon $\delta$ and Lebesgue time $t \in (0,\delta]$, consider the event that the process is still alive at time $t$ and that its position $Y_t$ lies in the drift-shifted chunk $dt + [a,b]$ while simultaneously lying on the lattice $h\mathbb{Z}$. This theorem asserts that the time-integrated probability of that joint event vanishes:
--
--   $$\int_0^\delta \mathbb{P}\big(t < \zeta,\ Y_t \in dt + [a,b],\ Y_t \in h\mathbb{Z}\big)\,dt = 0.$$
--
--   Mathematically this is the countable-bad-times step in the lattice case of Kyprianou's Theorem 5.4: for each lattice point and each jump size, the drift can carry the process onto the lattice only at isolated times, and a countable set of times has Lebesgue measure zero. It is the error term that lets the off-lattice occupation charge dominate the shifted-chunk charge.
--
--   Formalization note: all binders are those of the killed-subordinator framework of Chapter 5; the lattice event is stated as membership in $\{z \mid \exists n \in \mathbb{Z},\ z = n h\}$, complementary to the off-lattice set used in the parent node.
-- source:
--   Kyprianou, Fluctuations of Lévy Processes with Applications (2006), Ch. 5, Theorem 5.4

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

/-- The shifted chunk meets the lattice only at countably many times, so its
lattice-restricted occupation charge integrates to zero. -/
theorem killedPotential_shiftedChunk_lattice_integral_eq_zero
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
            Y (Real.toNNReal t) omega ∈ {z : Real | ∃ y ∈ Set.Icc a b, z = d * t + y} ∧
            Y (Real.toNNReal t) omega ∈ {z : Real | ∃ n : Int, z = (n : Real) * h}} ∂volume) = 0)
 := by
  sorry

end Kyprianou.Ch05
