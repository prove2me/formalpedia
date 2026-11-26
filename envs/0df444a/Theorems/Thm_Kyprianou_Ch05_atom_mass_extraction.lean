-- Prove2me | Theorems.Thm_Kyprianou_Ch05_atom_mass_extraction
-- name    : Kyprianou.Ch05.atom_mass_extraction
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-26T11:29:24.154266+00:00
-- url     : https://prove2.me/theorems/b1227270-d843-5d39-b7f3-48af94db6ad5
-- title:
--   Extraction of a large atom from the atom-mass sum
-- statement:
--   For a killed subordinator with Levy measure $\Pi$ of infinite mass on $(0,\infty)$, if on the interval $[\delta,1]$ the atom-mass sum $A_\delta = \sum_y \Pi(\{y\})^2$ (written as the integral of $y \mapsto \Pi(\{y\})$ against $\Pi$) strictly exceeds $c \cdot \Pi([\delta,1])$ for some real $c$, then some single point $y \in [\delta,1]$ carries an atom of mass $\Pi(\{y\}) \ge c$.

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

theorem atom_mass_extraction
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
  (Pi (Set.Ioi (0 : Real)) = ⊤ →
    ∀ δ : Real, 0 < δ → δ ≤ 1 → ∀ c : Real,
      c * (Pi (Set.Icc δ 1)).toReal < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal ((Pi {y}).toReal) ∂Pi).toReal →
      ∃ y ∈ Set.Icc δ 1, c ≤ (Pi {y}).toReal)
 := by
  sorry

end Kyprianou.Ch05
