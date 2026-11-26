-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedSubordinator_cesaro_sublevel_density
-- name    : Kyprianou.Ch05.killedSubordinator_cesaro_sublevel_density
-- status  : Open
-- author  : @pageman
-- created : 2026-11-26T04:12:57.967534+00:00
-- url     : https://prove2.me/theorems/617d1387-27e6-4c98-8158-160fde3ae9a8
-- title:
--   Cesaro density of sublevel sets of the characteristic exponent vanishes at infinite activity
-- statement:
--   Let $R(u)=\int_{(0,\infty)}(1-\cos(uy))\,\Pi(dy)$ be the real part of the characteristic exponent of a killed subordinator with infinite jump activity, $\Pi(0,\infty)=\infty$. Then for every level $K$ and every $\rho>0$, the sublevel set $\{u\ge 0 : R(u)\le K\}$ has Cesaro density at most $\rho$ for all large windows: there is $U_0$ such that for all $U\ge U_0$,\n\n$$\frac{1}{U}\,\bigl|\{u\in[0,U] : R(u)\le K\}\bigr| \le \rho.$$\n\nThis is the hard analytic core behind the Cesaro decay of $e^{-2tR(u)}$ in part (i) of Theorem 5.4 of Kyprianou (2006): on the sublevel set the exponential is merely bounded by $1$, and off it it is at most $e^{-2tK}$, so vanishing density of the sublevel set plus a large choice of $K$ closes the parent estimate.\n\n**Formalization Note.** $R(u)$ is written inline as the real part $(\int^-_{(0,\infty)} \mathrm{ofReal}(1-\cos(uy))\,d\Pi).\mathrm{toReal}$, matching the parent statement.
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

/-- Sublevel sets of the real part of the characteristic exponent have vanishing Cesaro density at infinite activity. -/
theorem killedSubordinator_cesaro_sublevel_density
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
    ∀ K : Real, ∀ ρ : ENNReal, 0 < ρ →
      ∃ U0 : Real, ∀ U : Real, U0 ≤ U → (∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal (if (∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume) * (ENNReal.ofReal U)⁻¹ ≤ ρ)
 := by
  sorry

end Kyprianou.Ch05
