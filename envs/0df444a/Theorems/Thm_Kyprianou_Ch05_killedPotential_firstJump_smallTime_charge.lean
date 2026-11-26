-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedPotential_firstJump_smallTime_charge
-- name    : Kyprianou.Ch05.killedPotential_firstJump_smallTime_charge
-- status  : Open
-- author  : @pageman
-- created : 2026-11-26T03:49:23.476694+00:00
-- url     : https://prove2.me/theorems/11cd9fb9-9a47-45c2-9335-81edebd6bc1e
-- title:
--   First-jump small-time asymptotics: positive off-lattice occupation charge near t=0
-- statement:
--   Let $Y$ be a killed subordinator with finite jump activity $\Pi(0,\infty)<\infty$ as in Theorem 5.4(ii) of Kyprianou (2006), and fix a span $h>0$ with $\Pi\{z:z\notin h\mathbb Z\}\ne 0$. Then the fixed-time off-lattice occupation probabilities charge a small-time interval uniformly: there exist $c>0$ and $\delta>0$ with $c \le \int_0^\delta \mathbb P(\text{alive at }t,\ Y_t\notin h\mathbb Z)\,dt$. Mechanism: as $t\to 0$ the integrand is asymptotic to $t\cdot\Pi(\text{off-lattice})$ up to the no-jump and two-jump errors, by the first-jump decomposition for finite-activity subordinators.
-- source:
--   Kyprianou (2006), first edition, Theorem 5.4, Section 5.1, printed pp. 114-115; first-jump child of Kyprianou.Ch05.killedPotential_firstJump_offLattice_charge (717cda54-49d3-5299-926d-190f0d836fa2).

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

/-- First-jump small-time charge: off-lattice Pi mass forces a positive occupation charge at small times. -/
theorem killedPotential_firstJump_smallTime_charge
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
    ∀ h : Real, 0 < h → Pi {z : Real | ∀ n : Int, z ≠ (n : Real) * h} ≠ 0 →
      ∃ c : ℝ≥0∞, 0 < c ∧ ∃ δ : Real, 0 < δ ∧
        c ≤ ∫⁻ t in Set.Ioc (0 : Real) δ,
          P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
            Y (Real.toNNReal t) omega ∈ {z : Real | ∀ n : Int, z ≠ (n : Real) * h}} ∂volume)
 := by
  sorry

end Kyprianou.Ch05
