-- Prove2me | Theorems.Thm_ModularCurve_exists_mem_riemannRochSpace_mapDomain_embDivisor_sub_notMem
-- name    : ModularCurve.exists_mem_riemannRochSpace_mapDomain_embDivisor_sub_notMem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/f430c3e9-2edc-5276-bfec-b008a0b9408d
-- title:
--   Degree 2g+1 reduced divisor separates rational points and tangents
-- statement:
--   Fix $N \ge 1$ and a valuation subring $A$ of $\overline{\mathbb Q}$, with residue field $k =$ `IsLocalRing.ResidueField A`. Let $R$ be a `ConstantReduction` of the field $\overline{\mathbb Q}F_N :=$ `modularFunctionFieldBar N` (the subfield of $\overline{\mathbb Q}((q))$ generated over $\overline{\mathbb Q}$ by the coefficientwise images of the full level-$N$ modular function field over $\mathbb Q$) along $A$ onto $\widetilde F_N :=$ `modularFunctionFieldFullC k N` (the subfield of $k((q))$ generated over $k$ by the level-$N$ divisor expansions over $k$); thus $R$ provides a valuation subring of $\overline{\mathbb Q}F_N$ whose intersection with $\overline{\mathbb Q}$ is $A$, a surjective residue map onto $\widetilde F_N$ with kernel the maximal ideal, and a degree-preserving map `R.placeMap` on places compatible with orders of reductions. Assume $R$ is good, i.e. $\mathrm{genusFF}(k,\widetilde F_N) = \mathrm{genusFF}(\overline{\mathbb Q},\overline{\mathbb Q}F_N) =: g$. Let $P, Q$ be places of $\widetilde F_N/k$ (not assumed distinct) that are rational, in the sense that $k$ surjects onto the residue field of the place. Write $\widetilde D$ for the pushforward along `R.placeMap` of `embDivisor N` $= (2g+1)\cdot$ `cuspInftyBar N`. The assertion is that there exists $u$ in the Riemann–Roch space $L(\widetilde D - P)$, i.e. with $v(u) \le \exp((\widetilde D - P)(v))$ for every place $v$, such that $u \notin L(\widetilde D - P - Q)$.
--
--   This is the point- and tangent-separation property of the complete linear system of degree $2g+1$ on the reduction of the modular curve, the reduction-side counterpart of the same statement over $\overline{\mathbb Q}$. It feeds the construction of chart data for a constant reduction, cited by [`ModularCurve.exists_constantReduction_chartData_of_isEmbBasis`](thm.html#ModularCurve.exists_constantReduction_chartData_of_isEmbBasis).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_mem_riemannRochSpace_mapDomain_embDivisor_sub_notMem.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_ModularCurve_ReductionModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_mem_riemannRochSpace_mapDomain_embDivisor_sub_notMem (N : ℕ) [NeZero N]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (R : ConstantReduction A (modularFunctionFieldBar N)
      (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N))
    (hR : R.IsGood)
    (P Q : Place (IsLocalRing.ResidueField A) (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N))
    (hP : P.IsRational) (hQ : Q.IsRational) :
    ∃ u ∈ riemannRochSpace (Finsupp.mapDomain R.placeMap (embDivisor N) - Finsupp.single P 1),
      u ∉ riemannRochSpace
        (Finsupp.mapDomain R.placeMap (embDivisor N) - Finsupp.single P 1 - Finsupp.single Q 1) := by sorry
