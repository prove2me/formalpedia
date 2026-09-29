-- Prove2me | Theorems.Thm_ModularCurve_IsPlaceReductionModL_apply_cuspInftyBar_eq_and_eq_cuspInftyBar_of_apply_eq_of_ord_ne_zero
-- name    : ModularCurve.IsPlaceReductionModL.apply_cuspInftyBar_eq_and_eq_cuspInftyBar_of_apply_eq_of_ord_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/c87195c5-d4f5-5071-a3c6-751de203788d
-- title:
--   Reduction mod ℓ carries the cusp ∞ to the q-adic place
-- statement:
--   Fix $N\ge 1$ and a prime $p$ not dividing $N$, and let $A$ be a valuation subring of $\overline{\mathbf Q}$ lying over $p$ in the sense that the image of $p$ belongs to the nonunits of $A$, with residue field $\kappa=\mathrm{ResidueField}\,A$ of characteristic $p$ and algebraically closed. Let $r$ assign to each place of $\mathrm{modularFunctionFieldBar}\,N$ — the subfield of $\overline{\mathbf Q}((q))$ generated over $\overline{\mathbf Q}$ by the coefficientwise images of $\mathrm{modularFunctionFieldFull}\,N$ — a place of $\mathrm{modularFunctionFieldFullC}\,\kappa\,N$, the subfield of $\kappa((q))$ generated over $\kappa$ by $\mathrm{divisorExpansionsC}\,\kappa\,N$; here a place is a valuation subring containing the constants, distinct from the whole field, and a principal ideal ring. Assume $r$ satisfies $\mathrm{IsPlaceReductionModL}\,A\,N\,r$: it preserves the degree of every place, and for every Laurent series $y$ with coefficients in $A$ whose image in $\overline{\mathbf Q}((q))$ lies in $\mathrm{modularFunctionFieldBar}\,N$ and whose coefficientwise reduction modulo the maximal ideal of $A$ is a nonzero element of $\mathrm{modularFunctionFieldFullC}\,\kappa\,N$, the pushforward along $r$ of the divisor of $y$ is the divisor of that reduction. Let $P_\infty$ be a place of $\mathrm{modularFunctionFieldFullC}\,\kappa\,N$ whose valuation subring consists exactly of those $f$ whose order as a Laurent series over $\kappa$ is $\ge 0$. Then $r(\mathrm{cuspInftyBar}\,N)=P_\infty$, where $\mathrm{cuspInftyBar}\,N$ is the $q$-adic place attached to the element $j$ given by the coefficientwise image of the $q$-expansion $\mathrm{jq}$, which has order $-1$; and, conversely, any place $w$ with $r(w)=P_\infty$ and $\mathrm{ord}_w(j)\ne 0$ equals $\mathrm{cuspInftyBar}\,N$.
--
--   This is the modular-curve instance of Deuring's reduction theory of function fields with respect to a prime divisor of the constant field: the cusp $\infty$ of $X_0(N)$ in characteristic $0$ reduces to the $q$-adic cusp of the special fibre, and no other zero or pole of $j$ does so. It is used in identifying the stalk of $j$ at the cusp section of the rational model of the curve, towards good reduction of $X_0(N)$ away from $N$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IsPlaceReductionModL_apply_cuspInftyBar_eq_and_eq_cuspInftyBar_of_apply_eq_of_ord_ne_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicCurve IsLocalRing
open ModularCurve

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.IsPlaceReductionModL.apply_cuspInftyBar_eq_and_eq_cuspInftyBar_of_apply_eq_of_ord_ne_zero
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
      Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N))
    (hr : IsPlaceReductionModL A N r)

    (Pinf : Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N))
    (hPinf : ∀ f : modularFunctionFieldFullC (ResidueField ↥A) N,
      f ∈ Pinf.toValuationSubring ↔ 0 ≤ ((f : modularFunctionFieldFullC (ResidueField ↥A) N) : LaurentSeries (ResidueField ↥A)).order) :
    r (cuspInftyBar N) = Pinf ∧
    ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), r w = Pinf →
      w.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N) ≠ 0 → w = cuspInftyBar N := by sorry
