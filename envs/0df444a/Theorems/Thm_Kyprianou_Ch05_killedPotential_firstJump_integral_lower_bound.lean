-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedPotential_firstJump_integral_lower_bound
-- name    : Kyprianou.Ch05.killedPotential_firstJump_integral_lower_bound
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-26T03:51:31.8718+00:00
-- url     : https://prove2.me/theorems/77564f3e-57ed-5561-b50f-c77c973716a1
-- title:
--   Occupation lower bound: small-time charge bounds the discounted potential integral below
-- statement:
--   With $Y$, $P$, $\mathrm{death}$ as in Theorem 5.4 of Kyprianou (2006), fix a span $h$, a discount rate $q\ge 0$, a time horizon $\delta$, and a constant $c$ bounded above by the small-time occupation integral $\int_0^\delta \mathbb P(\text{alive at }t,\ Y_t\notin h\mathbb Z)\,dt$. Then $e^{-q\delta}$ times $c$ (in extended nonnegative reals) is at most the full discounted occupation integral $\int_0^\infty e^{-qt}\,\mathbb P(\text{alive at }t,\ Y_t\notin h\mathbb Z)\,dt$ that defines the potential $U^q$ off the lattice. The proof is pure monotonicity: on $[0,\delta]$ the discount factor $e^{-qt}$ is at least $e^{-q\delta}$, and enlarging the interval only increases the integral.
-- source:
--   Kyprianou (2006), first edition, Theorem 5.4, Section 5.1, printed pp. 114-115; occupation-glue child of Kyprianou.Ch05.killedPotential_firstJump_offLattice_charge (717cda54-49d3-5299-926d-190f0d836fa2).

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

/-- Occupation lower bound: a uniform small-time charge on the off-lattice occupation probabilities bounds the discounted potential integrand below. -/
theorem killedPotential_firstJump_integral_lower_bound
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
  (∀ h : Real, ∀ q : Real, 0 ≤ q → ∀ δ : Real, ∀ c : ℝ≥0∞,
    c ≤ ∫⁻ t in Set.Ioc (0 : Real) δ,
          P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
            Y (Real.toNNReal t) omega ∈ {z : Real | ∀ n : Int, z ≠ (n : Real) * h}} ∂volume →
    ENNReal.ofReal (Real.exp (-q * δ)) * c ≤
      ∫⁻ t in Set.Ici (0 : Real),
        ENNReal.ofReal (Real.exp (-q * t)) *
          P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
            Y (Real.toNNReal t) omega ∈ {z : Real | ∀ n : Int, z ≠ (n : Real) * h}} ∂volume)
 := by
  sorry

end Kyprianou.Ch05
