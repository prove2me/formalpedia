-- Prove2me | Theorems.Thm_Kyprianou_Ch05_regularVariationTailLimitAtInfinity
-- name    : Kyprianou.Ch05.regularVariationTailLimitAtInfinity
-- status  : Open
-- author  : @daga2
-- created : 2026-11-26T03:14:15.959311+00:00
-- url     : https://prove2.me/theorems/f750435d-8a70-4756-b84f-262947dff3a5
-- title:
--   Lemma 5.17, infinity regime: L\'evy-tail limit
-- statement:
--   Let $Y$ be a subordinator killed at rate $0$, with Laplace exponent $\Phi$, L\'evy measure $\Pi$, drift $d$, and $0$-potential family $U$. Let $\alpha \in [0,1)$ and suppose $\Phi$ is regularly varying at infinity with index $\alpha$. Then the jump tail satisfies
--
--   $$
--   \frac{\Pi((\lambda x, \infty))}{\Phi(1/x)} \to \frac{\lambda^{-\alpha}}{\Gamma(1-\alpha)} \qquad (x \to 0^+)
--   $$
--
--   for every $\lambda > 0$. This is the second numbered conclusion of Lemma 5.17 in the regular-variation-at-infinity regime. The hypothesis $\alpha < 1$ is sharp: at $\alpha = 1$ the constant $1/\Gamma(1-\alpha)$ is not defined.
--
--   **Formalization Note** $\Pi((\lambda x, \infty))$ is the real number obtained from the measure of the open interval, and the limit is a `Filter.Tendsto` statement in `nhdsWithin 0 (Set.Ioi 0)`.
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

theorem regularVariationTailLimitAtInfinity
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
    (hRV : RegularlyVaryingAtInfinity Phi alpha) (halt : alpha < 1) :
  (∀ lambda : Real, 0 < lambda →
          Tendsto
            (fun x : Real =>
              (Pi (Set.Ioi (lambda*x))).toReal / Phi (1 / x))
            (nhdsWithin (0 : Real) (Set.Ioi 0))
            (nhds (lambda ^ (-alpha) / Real.Gamma (1-alpha)))) := by
  sorry

end Kyprianou.Ch05
