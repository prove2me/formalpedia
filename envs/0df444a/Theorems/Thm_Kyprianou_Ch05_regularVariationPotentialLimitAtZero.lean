-- Prove2me | Theorems.Thm_Kyprianou_Ch05_regularVariationPotentialLimitAtZero
-- name    : Kyprianou.Ch05.regularVariationPotentialLimitAtZero
-- status  : Open
-- author  : @daga2
-- created : 2026-11-26T03:14:02.783553+00:00
-- url     : https://prove2.me/theorems/7d99f18f-a66a-5f44-b5fb-653de24a9291
-- title:
--   Lemma 5.17, zero regime: potential-mass limit
-- statement:
--   Let $Y$ be a subordinator killed at rate $0$, with Laplace exponent $\Phi$, L\'evy measure $\Pi$, drift $d$, and $0$-potential family $U$. Let $\alpha \in [0,1]$ and suppose $\Phi$ is regularly varying at $0$ with index $\alpha$. Then the potential mass of $[0, \lambda x]$ satisfies
--
--   $$
--   U_0([0, \lambda x]) \cdot \Phi(1/x) \to \frac{\lambda^\alpha}{\Gamma(1+\alpha)} \qquad (x \to \infty)
--   $$
--
--   for every $\lambda > 0$. This is the first numbered conclusion of Lemma 5.17 in the regular-variation-at-zero regime: the Tauberian companion of the Laplace identity $\int e^{-\theta y} U_0(dy) = 1/\Phi(\theta)$ under Karamata's theorem.
--
--   **Formalization Note** $U_0$ is the undiscounted potential measure from `IsKilledPotentialFamily`, and the limit is a `Filter.Tendsto` statement at `atTop`.
-- source:
--   Kyprianou (2006), first edition, result 5.17, printed pages 121, 130 or 132.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_WeakPassageObservables
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

theorem regularVariationPotentialLimitAtZero
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : IsKilledSubordinator P Y death 0)
    (hTriplet : IsKilledLaplaceTriplet 0 d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * Phi theta))
    (hLeft : IsLeftLimitVersion P Y Yleft)
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U)
    (alpha : Real) (hAlpha : 0 ≤ alpha ∧ alpha ≤ 1)
    (hRV : RegularlyVaryingAtZero Phi alpha) :
  (∀ lambda : Real, 0 < lambda →
        Tendsto
          (fun x : Real =>
            ((U 0) (Set.Icc (0 : Real) (lambda * x))).toReal *
              Phi (1 / x))
          atTop
          (nhds (lambda ^ alpha / Real.Gamma (1+alpha)))) := by
  sorry

end Kyprianou.Ch05
