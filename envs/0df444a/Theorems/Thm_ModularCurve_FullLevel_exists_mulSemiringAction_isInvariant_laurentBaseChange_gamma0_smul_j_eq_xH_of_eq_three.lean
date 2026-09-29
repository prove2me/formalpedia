-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_mulSemiringAction_isInvariant_laurentBaseChange_gamma0_smul_j_eq_xH_of_eq_three
-- name    : ModularCurve.FullLevel.exists_mulSemiringAction_isInvariant_laurentBaseChange_gamma0_smul_j_eq_xH_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/0fa6ceb8-1905-52b6-9e1a-c5cdde02463a
-- title:
--   Diamond group action on the X_H(q²M') function field, q=3
-- statement:
--   Let $q$ be a prime with $q = 3$, let $M'$ be a nonzero natural number not divisible by $q$, and let $L$ be a field of characteristic zero. Write $H =$ [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22) for the kernel of the reduction map $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$. Let $K$ be an intermediate field of $L \subseteq L((\mathsf q))$ equal to [`ModularCurve.laurentBaseChange L`](def/ModularCurve_LaurentCoeff.html#L103) applied to the $q$-expansion function field [`ModularCurve.xHFunctionField (q ^ 2 * M') H`](def/ModularCurve_XH.html#L79), that is, the subfield of $L((\mathsf q))$ generated over $L$ by the image of that field of rational Laurent series under the coefficientwise embedding induced by $\mathbb{Q} \to L$. Let $j \in K$ be an element whose underlying Laurent series is the image under that coefficientwise embedding of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157), the $q$-expansion $\mathsf q^{-1}\cdot(\text{integral numerator series})$ of the $j$-invariant. Let $K_2$ be the analogous base change to $L$ of [`ModularCurve.modularFunctionFieldFull (q ^ 2 * M')`](def/ModularCurve_X0.html#L305), the subfield of $\mathbb{Q}((\mathsf q))$ generated over $\mathbb{Q}$ by the expansions $j(\mathsf q^d)$ for the nonzero divisors $d$ of $q^2M'$, and assume $K_2 \le K$. The conclusion asserts the existence of a type $G$ carrying a group structure, a `Fintype` structure and an action of $G$ on $K$ by ring automorphisms, such that, with $K$ regarded as a $K_2$-algebra via the inclusion $K_2 \le K$, the $G$-action commutes with the $K_2$-action and $K_2$ is exactly the subalgebra of $G$-invariants of $K$ (`Algebra.IsInvariant`), the $G$-action commutes with the $L$-action on $K$, the $G$-action on $K$ is faithful, and every $g \in G$ fixes $j$.
--
--   This packages the diamond operators: the action of $\Gamma_0(q^2M')/\Gamma_H(q^2M')$ on the covering $X_H(q^2M') \to X_0(q^2M')$, realised as a finite faithful group of $L$-algebra automorphisms of the base-changed $q$-expansion function field whose invariant subfield is the $\Gamma_0$-level field and which fixes the $j$-invariant. It is the $q=3$ case of the statement used in the analysis of the $\infty$-branch of the relevant semistable covering, and is cited in the study of minimal primes over the span of the $j$-invariant chart at infinity and in the construction of the corresponding action on the chart algebra at infinity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_mulSemiringAction_isInvariant_laurentBaseChange_gamma0_smul_j_eq_xH_of_eq_three.lean

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.FullLevel.exists_mulSemiringAction_isInvariant_laurentBaseChange_gamma0_smul_j_eq_xH_of_eq_three
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq)
    (K₂ : IntermediateField L (LaurentSeries L))
    (hK₂ : K₂ = ModularCurve.laurentBaseChange L (ModularCurve.modularFunctionFieldFull (q ^ 2 * M')))
    (hle : K₂ ≤ K) :
    ∃ (G : Type) (_ : Group G) (_ : Fintype G) (_ : MulSemiringAction G ↥K),
      (letI := (IntermediateField.inclusion hle).toRingHom.toAlgebra
       SMulCommClass G ↥K₂ ↥K ∧ Algebra.IsInvariant ↥K₂ ↥K G) ∧
      SMulCommClass G L ↥K ∧ FaithfulSMul G ↥K ∧
      (∀ g : G, g • j = j) := by sorry
