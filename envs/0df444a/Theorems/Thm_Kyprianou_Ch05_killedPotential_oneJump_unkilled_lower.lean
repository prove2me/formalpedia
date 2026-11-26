-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedPotential_oneJump_unkilled_lower
-- name    : Kyprianou.Ch05.killedPotential_oneJump_unkilled_lower
-- status  : Open
-- author  : @pageman
-- created : 2026-11-26T12:14:00.905315+00:00
-- url     : https://prove2.me/theorems/95d8c1c2-1559-5417-be6a-958a6ef1efcb
-- title:
--   Unkilled one-jump lower bound for the drift-shifted chunk
-- statement:
--   Let $Y$ be a subordinator with Laplace triplet $(\eta, d, \Pi)$ whose Lévy measure has finite total mass $\Pi(0,\infty) < \infty$. For every $0 < a \le b$ there is $\delta > 0$ such that for all $0 < t \le \delta$, $P(Y_t \in d t + [a,b]) \ge \frac{3t}{4} \Pi([a,b])$: the one-jump contribution, with the constant $3/4$ leaving room for the independent survival factor in the killed parent statement.
-- source:
--   Kyprianou (2006), Fluctuations of Lévy Processes, Ch. 5, Thm 5.4 proof (one-jump lower bound); decomposition child of killedPotential_oneJump_shiftedChunk_pointwise

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

/-- Unkilled one-jump lower bound for the drift-shifted chunk. -/
theorem killedPotential_oneJump_unkilled_lower
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : IsKilledSubordinator P Y death eta)
    (hTriplet : IsKilledLaplaceTriplet eta d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * (Phi theta - eta))) :
  (Pi (Set.Ioi (0 : Real)) < ⊤ →
    ∀ a b : Real, 0 < a → a ≤ b →
      ∃ δ : Real, 0 < δ ∧ ∀ t ∈ Set.Ioc (0 : Real) δ,
        ENNReal.ofReal (3 * t / 4) * Pi (Set.Icc a b) ≤
          P {omega : Omega | Y (Real.toNNReal t) omega ∈
            {z : Real | ∃ y ∈ Set.Icc a b, z = d * t + y}})
 := by
  sorry

end Kyprianou.Ch05
