-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_gcd_natAbs_ord_eisensteinRatio_pow_eq_one_of_mem_ssPlaces
-- name    : ModularCurve.FullLevel.gcd_natAbs_ord_eisensteinRatio_pow_eq_one_of_mem_ssPlaces
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/7bf10d49-6b0e-5e89-a217-476c6c98ff51
-- title:
--   Order of the Eisenstein radicand at supersingular places
-- statement:
--   Let $q$ be a prime with $q \ge 5$, let $M'$ be a nonzero natural number with $q \nmid M'$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ satisfying `LiesOverPrime q`, i.e. the image of $q$ lies in the non-units of $A$; write $\kappa$ for the residue field $A/\mathfrak m_A$. Inside the Laurent series field $\kappa((X))$ consider the intermediate field $\kappa(\,$`jqModC`$\,\kappa,\,$`jqNModC`$\,\kappa\,M')$ generated over $\kappa$ by the $q$-expansion of $j$ and its $M'$-fold expansion, and let $b$ be an element of it whose Laurent series equals $$\Bigl(\tfrac{\bar E_4\,\bar E_6}{\overline{X\cdot\eta^{24}}}\Bigr)^{(q-1)/2},$$ where $\bar E_4$, $\bar E_6$ are the mod-$\mathfrak m_A$ reductions of the power series with $n$-th coefficients $240\,\sigma_3(n)$ and $-504\,\sigma_5(n)$ for $n \ge 1$ and constant term $1$, the denominator is the reduction of $X\prod_{n\ge 1}(1-X^{n})^{24}$, and $(q-1)/2$ denotes natural-number division. Let $v$ be a place of this field over $\kappa$ (a proper valuation subring containing $\kappa$ and being a principal ideal ring) which lies in `ssPlaces q M' κ`, i.e. $v$ is rational, is an affine geometric place, and the value of `jGeomGen` at $v$ lies in the supersingular $j$-set `ssJSet q κ`. Then $\gcd\bigl((q-1)/2,\ |\operatorname{ord}_v b|\bigr) = 1$, where $\operatorname{ord}_v$ is the normalised integer valuation attached to $v$.
--
--   The element $b$ is the Kummer radicand cutting out the Igusa level-$q$ covering of $X_0(M')$ in characteristic $q$, and the coprimality asserted here is exactly what makes the Kummer ramification formula $e = n/\gcd(n,\operatorname{ord}_v b)$ give full ramification $e = (q-1)/2$ at the supersingular places. It is used in the computation of the ramification index of the level-$\Gamma_H$ function field over the function field of $X_0(M')$ at places lying over $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_gcd_natAbs_ord_eisensteinRatio_pow_eq_one_of_mem_ssPlaces.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringGuards
import Definitions.Def_AlgebraicCurve_DivisorPushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing
open scoped ArithmeticFunction.sigma

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.gcd_natAbs_ord_eisensteinRatio_pow_eq_one_of_mem_ssPlaces
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (b : ↥(modularFunctionFieldC (ResidueField A) M'))
    (hb : (b : LaurentSeries (ResidueField A)) =
        (ModularCurve.intSeriesC (ResidueField A) (PowerSeries.mk fun n => if n = 0 then 1 else 240 * (σ 3 n : ℤ)) *
            ModularCurve.intSeriesC (ResidueField A) (PowerSeries.mk fun n => if n = 0 then 1 else -504 * (σ 5 n : ℤ)) /
          ModularCurve.intSeriesC (ResidueField A) (PowerSeries.X * ModularCurve.dedekindEtaUnit)) ^ ((q - 1) / 2))
    (v : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) M'))
    (hv : v ∈ ssPlaces q M' (ResidueField A)) :
    Nat.gcd ((q - 1) / 2) (v.ord b).natAbs = 1 := by sorry
