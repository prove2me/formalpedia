-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedPotential_offLattice_chunk
-- name    : Kyprianou.Ch05.killedPotential_offLattice_chunk
-- status  : Open
-- author  : @pageman
-- created : 2026-11-26T04:13:17.530959+00:00
-- url     : https://prove2.me/theorems/d743dc9d-1a3d-5eff-a113-521ae70df008
-- title:
--   Off-lattice Pi mass contains a closed interval chunk of positive Pi measure
-- statement:
--   Let $Y$ be a killed subordinator with finite jump activity, $\Pi(0,\infty)<\infty$, as in Theorem 5.4(ii) of Kyprianou (2006). Fix a span $h>0$. If $\Pi$ puts nonzero mass off the lattice $h\mathbb Z$, then that mass localizes to a single closed interval: there exist $0<a\le b$ such that the whole interval $[a,b]$ avoids $h\mathbb Z$ and $\Pi([a,b])>0$.
--
--   $$\Pi\{z:z\notin h\mathbb Z\}\ne 0\ \Longrightarrow\ \exists\,0<a\le b,\ [a,b]\cap h\mathbb Z=\varnothing,\ \Pi([a,b])>0.$$
--
--   The off-lattice set is open in $(0,\infty)$ (its complement $h\mathbb Z$ is closed), and a finite measure gives an open set of positive measure an interval of positive measure inside it. This chunk is the input to the first-jump small-time charge estimate behind `killedPotential_firstJump_smallTime_charge`.
--
--   **Formalization Note.** Same binder block as `killedPotential_firstJump_smallTime_charge`; the conclusion is purely about $\Pi$ and $h$.
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

/-- Off-lattice mass localizes to a closed interval avoiding the lattice. -/
theorem killedPotential_offLattice_chunk
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
      ∃ a b : Real, 0 < a ∧ a ≤ b ∧
        (∀ z ∈ Set.Icc a b, ∀ n : Int, z ≠ (n : Real) * h) ∧
        0 < Pi (Set.Icc a b))
 := by
  sorry

end Kyprianou.Ch05
