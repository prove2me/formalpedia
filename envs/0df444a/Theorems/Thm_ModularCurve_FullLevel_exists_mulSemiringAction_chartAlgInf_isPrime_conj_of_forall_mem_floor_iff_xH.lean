-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_mulSemiringAction_chartAlgInf_isPrime_conj_of_forall_mem_floor_iff_xH
-- name    : ModularCurve.FullLevel.exists_mulSemiringAction_chartAlgInf_isPrime_conj_of_forall_mem_floor_iff_xH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/48200765-ca46-53b1-9934-1e3547451845
-- title:
--   Diamond operators act transitively on primes of the pole chart
-- statement:
--   Let $q \ge 5$ be a prime with $q \nmid M'$ and $M' \neq 0$, let $L$ be a field of characteristic $0$, and let $K$ be an intermediate field of $L \subseteq L(\!(t)\!)$ equal to [`ModularCurve.laurentBaseChange L`](def/ModularCurve_LaurentCoeff.html#L103) applied to the $q$-expansion function field `xHFunctionField (q ^ 2 * M') (levelH q M')`, i.e. the subfield of $L(\!(t)\!)$ generated over $L$ by the coefficientwise images under $\mathbb{Q} \to L$ of that field, where `levelH q M'` is the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$. Let $A$ be a commutative ring with compatible algebra structures on $L$ and on $K$, and let $j \in K$ have as its image in $L(\!(t)\!)$ the coefficientwise image of the $q$-expansion `jq`. Then there is a finite group $G$ acting on $K$ by ring automorphisms, commuting with the $L$-action, such that: every $g \in G$ fixes each $x \in K$ whose image lies in `laurentBaseChange L (modularFunctionFieldFull (q ^ 2 * M'))`; conversely every $G$-invariant element of $K$ lies in that subfield; every $g$ fixes the image of $A$ and fixes $j$; the subalgebra `chartAlgInf A K j` of elements of $K$ integral over $A[j^{-1}]$ is stable under $G$; and for prime ideals $y, y'$ of that subalgebra which contain the same elements $b$ whose image in $L(\!(t)\!)$ lies in the above subfield, there is $g \in G$ such that for all $b, b'$ in the subalgebra with $b' = g \cdot b$ in $K$ one has $b \in y \iff b' \in y'$.
--
--   This packages the action of the diamond operators on the function field of $X_H(q^2 M')$ over the floor $X_0(q^2 M')$, together with stability of the pole chart (the integral closure of $A[1/j]$) and transitivity of the action on the primes of that chart lying over a given prime of the floor. It is the group-theoretic input to the regularity statement for the cuspidal fibre of the infinity chart, [`ModularCurve.FullLevel.isRegularLocalRing_fibre_of_isLocalization_atPrime_chartAlgInf_of_forall_mem_nonunits_gauss_xH_of_isAlgebraic`](thm.html#ModularCurve.FullLevel.isRegularLocalRing_fibre_of_isLocalization_atPrime_chartAlgInf_of_forall_mem_nonunits_gauss_xH_of_isAlgebraic); the group and the two floor clauses come from [`ModularCurve.FullLevel.exists_mulSemiringAction_isInvariant_laurentBaseChange_gamma0_smul_j_eq_xH`](thm.html#ModularCurve.FullLevel.exists_mulSemiringAction_isInvariant_laurentBaseChange_gamma0_smul_j_eq_xH), the identification of the floor using [`ModularCurve.laurentBaseChange_qExpFunctionFieldC_eq`](thm.html#ModularCurve.laurentBaseChange_qExpFunctionFieldC_eq) and [`ModularCurve.qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull`](thm.html#ModularCurve.qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_mulSemiringAction_chartAlgInf_isPrime_conj_of_forall_mem_floor_iff_xH.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.FullLevel.exists_mulSemiringAction_chartAlgInf_isPrime_conj_of_forall_mem_floor_iff_xH
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (A : Type) [CommRing A] [Algebra A L] [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) :
    ∃ (G : Type) (_ : Group G) (_ : Fintype G) (_ : MulSemiringAction G ↥K),
      SMulCommClass G L ↥K ∧

      (∀ (g : G) (x : ↥K), (x : LaurentSeries L) ∈ ModularCurve.laurentBaseChange L (ModularCurve.modularFunctionFieldFull (q ^ 2 * M')) → g • x = x) ∧
      (∀ x : ↥K, (∀ g : G, g • x = x) → (x : LaurentSeries L) ∈ ModularCurve.laurentBaseChange L (ModularCurve.modularFunctionFieldFull (q ^ 2 * M'))) ∧

      (∀ (g : G) (a : A), g • algebraMap A ↥K a = algebraMap A ↥K a) ∧
      (∀ g : G, g • j = j) ∧
      (∀ (g : G) (b : ↥K), b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A ↥K j → g • b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A ↥K j) ∧

      (∀ (y y' : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A ↥K j)), y.IsPrime → y'.IsPrime →
        (∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A ↥K j), ((b : ↥K) : LaurentSeries L) ∈ ModularCurve.laurentBaseChange L (ModularCurve.modularFunctionFieldFull (q ^ 2 * M')) → (b ∈ y ↔ b ∈ y')) →
        ∃ g : G, ∀ b b' : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A ↥K j), (b' : ↥K) = g • (b : ↥K) → (b ∈ y ↔ b' ∈ y')) := by sorry
