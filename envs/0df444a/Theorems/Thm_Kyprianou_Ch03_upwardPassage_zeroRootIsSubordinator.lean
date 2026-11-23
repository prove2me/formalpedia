-- Prove2me | Theorems.Thm_Kyprianou_Ch03_upwardPassage_zeroRootIsSubordinator
-- name    : Kyprianou.Ch03.upwardPassage_zeroRootIsSubordinator
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T19:28:50.260641+00:00
-- url     : https://prove2.me/theorems/894d131f-3c20-404c-af07-b5b7852c7c3c
-- title:
--   Upward first-passage time process is a subordinator when $\Phi(0) = 0$
-- statement:
--   Let $X = (X_t)_{t \ge 0}$ be a spectrally negative Lévy process on a filtered probability space $(\Omega, \mathcal{F}, P)$ whose paths are not almost surely nonincreasing, and suppose $\theta = 0$ is the unique nonnegative root of its Laplace exponent $\psi(\theta) = 0$ (so $\Phi(0) = 0$, meaning $X$ either oscillates or drifts to $+\infty$).
--
--   Then there exists a measurable real-valued subordinator $S = (S_x)_{x \ge 0}$ on $(\Omega, P)$ whose path-space law as a $[0, \infty]$-valued process matches the upward first-passage time process $\tau^+ = (\tau_x^+)_{x \ge 0}$, where $\tau_x^+ = \inf\{t > 0 : X_t > x\}$:
--   $$\operatorname{Law}_P\!\bigl((S_x^+)_{x \ge 0}\bigr) = \operatorname{Law}_P\!\bigl((\tau_x^+)_{x \ge 0}\bigr)$$
--   on $[0, \infty]^{[0, \infty)}$.
-- source:
--   Kyprianou (2006), Introductory Lectures on Fluctuations of Lévy Processes with Applications, Chapter 3, §3.3, Theorem 3.12 and Corollary 3.14 (pp. 81–84)

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem upwardPassage_zeroRootIsSubordinator
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂ P,
      Antitone (fun t : NNReal => L.X t omega)))
    (hZeroRoot : forall theta : Real, 0 <= theta -> L.ψ theta = 0 -> theta = 0) :
    exists (S : NNReal -> Omega -> Real),
      IsSubordinator P S ∧
      (forall x : NNReal, Measurable (S x)) ∧
      Measure.map
        (fun omega : Omega =>
          fun x : NNReal =>
            (Real.toNNReal (S x omega) : WithTop NNReal)) P =
      Measure.map
        (fun omega : Omega =>
          fun x : NNReal =>
            firstHittingTime L.X (Set.Ioi (x : Real)) omega) P := by
  sorry

end Kyprianou.Ch03
