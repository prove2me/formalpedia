-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedSubordinator_cesaro_sublevel_density_restricted
-- name    : Kyprianou.Ch05.killedSubordinator_cesaro_sublevel_density_restricted
-- status  : Open
-- author  : @pageman
-- created : 2026-11-26T09:23:52.071888+00:00
-- url     : https://prove2.me/theorems/b2fb9ff2-b1c6-51d4-947c-e02229a8cbec
-- title:
--   Cesaro density of sublevel sets of the characteristic exponent vanishes at infinite activity (restricted exponent)
-- statement:
--   Let $R_\delta(u)=\int_{[\delta,1]}(1-\cos(uy))\,\Pi(dy)$ be the real part of the characteristic exponent of a killed subordinator restricted to jumps of size in $[\delta,1]$, where $\Pi(0,\infty)=\infty$. Then for every level $K$ and every $\rho>0$ there exist $\delta\in(0,1]$ and $U_0$ such that for all $U\ge U_0$, $$\frac{1}{U}\,\bigl|\{u\in[0,U] : R_\delta(u)\le K\}\bigr| \le \rho.$$ This is the Bohr-mean / small-jump core of the vanishing Cesaro density of sublevel sets of the full exponent: once the exponent is truncated away from $0$, the sublevel density is governed by the almost-periodic mean of $1-\cos(uy)$ over the window $[\delta,1]$, and the parent statement follows by pointwise monotonicity of the exponent in the integration region together with finiteness of the full exponent.
-- source:
--   Kyprianou (2006), first edition, Theorem 5.4, Section 5.1, printed pp. 114-115; decomposition child of Kyprianou.Ch05.killedSubordinator_cesaro_sublevel_density (617d1387-27e6-4c98-8158-160fde3ae9a8).

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

/-- Cesaro density of sublevel sets of the characteristic exponent, restricted exponent: the same vanishing-density statement with the real part of the exponent truncated to jumps in [δ, 1]. -/
theorem killedSubordinator_cesaro_sublevel_density_restricted
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
      ∃ δ : Real, 0 < δ ∧ δ ≤ 1 ∧ ∃ U0 : Real, ∀ U : Real, U0 ≤ U →
        (∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal (if (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume) * (ENNReal.ofReal U)⁻¹ ≤ ρ)
 := by
  sorry

end Kyprianou.Ch05
