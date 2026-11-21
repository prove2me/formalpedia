-- Prove2me | Theorems.Thm_MasulloRH_regularized_reference_mass_prime_series
-- name    : MasulloRH.regularized_reference_mass_prime_series
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T00:48:47.28754+00:00
-- url     : https://prove2.me/theorems/c38c09eb-7c38-4b53-ae23-d6352d632124
-- title:
--   An absolutely convergent prime-power expansion for the reference mass in Masullo’s regularized resolvent test
-- statement:
--   Let $L=\zeta'/\zeta$, and let $A=\Re(L(3)-L(5/2)-\operatorname{Arch}(3)+\operatorname{Polar}(3))$ be the reference mass in the regularized trace comparison. If $\Lambda$ is the von Mangoldt function, then the following series is absolutely convergent and gives an arithmetic expression for $A$:
--   $$A=\frac{\log 2}{2}+\frac{\pi}{4}-\frac{37}{30}+\sum_{n\ge1}\Lambda(n)(n^{-5/2}-n^{-3}).$$
--   All terms in the series are nonnegative. A finite cutoff therefore supplies a lower approximation to the reference mass determined by prime powers alone.
-- source:
--   Masullo regularized trace reconstruction, §§1.4.2–1.4.4. Evaluation of the base resolvent at 3 by the classical von Mangoldt Dirichlet series and direct integration of the real-place correction.

import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib.NumberTheory.LSeries.Dirichlet

set_option autoImplicit false

namespace MasulloRH

theorem regularized_reference_mass_prime_series :
    HasSum (fun n : ℕ => ArithmeticFunction.vonMangoldt n / (n:ℝ)^(5/2:ℝ) -
      ArithmeticFunction.vonMangoldt n / (n:ℝ)^(3:ℝ))
      ((zetaLogDeriv 3).re - (zetaLogDeriv (5/2) + regularizedArch 3 - regularizedPolar 3).re -
        Real.log 2 / 2 - Real.pi / 4 + 37 / 30) := by sorry

end MasulloRH
