-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedPotential_lintegral_formula
-- name    : Kyprianou.Ch05.killedPotential_lintegral_formula
-- status  : Open
-- author  : @pageman
-- created : 2026-11-26T03:19:38.385377+00:00
-- url     : https://prove2.me/theorems/fffb35af-3922-55f0-aa75-a8af07a2b801
-- title:
--   Lintegral of the killed q-potential as a time integral
-- statement:
--   The $q$-potential $U^q$ of a killed subordinator is defined by its values on measurable sets, as the discounted expected occupation integral. This lemma is the Tonelli form of that definition: for every measurable $f:\mathbb R\to[0,\infty]$ and $q\ge 0$,
--
--   $$\int f(x)\,U^q(dx)=\int_0^\infty e^{-qt}\int_{\{\text{alive at }t\}} f(Y_t)\,dP\,dt.$$
--
--   It is the transport step that turns set-level potential identities into transform identities, in particular the resolvent formula of Theorem 5.4 of Kyprianou (2006).
--
--   **Formalization Note.** The inner integral is over the survival event $\{(t:\text{WithTop}\,\mathbb R_{\ge0})<\mathrm{death}\}$, exactly as in `IsKilledPotential`.
-- source:
--   Kyprianou (2006), first edition, Theorem 5.4, Section 5.1, printed pp. 114-115; decomposition of Kyprianou.Ch05.killedSubordinatorPotentialLattice (931e3306-d573-44a6-a001-adf4e80d2053) and its children.

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

/-- Tonelli form of the exact killed potential occupation formula. -/
theorem killedPotential_lintegral_formula
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
  ∀ q : Real, 0 ≤ q → ∀ f : Real → ENNReal, Measurable f →
      (∫⁻ x : Real, f x ∂(U q)) =
        ∫⁻ t in Set.Ici (0 : Real),
          ENNReal.ofReal (Real.exp (-q * t)) *
          ∫⁻ omega in {omega : Omega |
            (Real.toNNReal t : WithTop NNReal) < death omega},
            f (Y (Real.toNNReal t) omega) ∂P ∂volume
 := by
  sorry

end Kyprianou.Ch05
