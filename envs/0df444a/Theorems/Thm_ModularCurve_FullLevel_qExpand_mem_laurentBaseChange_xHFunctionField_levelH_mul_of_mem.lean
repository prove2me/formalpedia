-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_qExpand_mem_laurentBaseChange_xHFunctionField_levelH_mul_of_mem
-- name    : ModularCurve.FullLevel.qExpand_mem_laurentBaseChange_xHFunctionField_levelH_mul_of_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/232f524c-cede-5aa6-9ffc-39e93d130853
-- title:
--   Substitution mathsf q↦mathsf q^q raises level ℓ' to qℓ'
-- statement:
--   Let $q$ and $\ell'$ be primes, let $M'$ be a nonzero natural number, and let $L$ be a field of characteristic $0$. Write $\mathrm{levelH}\,n\,M'$ for the kernel of the reduction map $(\mathbb Z/n^{2}M')^{\times}\to(\mathbb Z/n)^{\times}$ induced by $n\mid n^{2}M'$, and $\mathrm{xHFunctionField}\,M\,H$ for the intermediate field [`ModularCurve.qExpFunctionFieldC`](def/ModularCurve_X1.html#L101) of $\mathbb Q\subseteq\mathbb Q(\!(\mathsf q)\!)$ attached to the congruence subgroup [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133); for an intermediate field $F_0$ of $\mathbb Q(\!(\mathsf q)\!)$, $\mathrm{laurentBaseChange}\,L\,F_0$ is the intermediate field of $L\subseteq L(\!(\mathsf q)\!)$ generated over $L$ by the image of $F_0$ under the coefficientwise map $\mathbb Q(\!(\mathsf q)\!)\to L(\!(\mathsf q)\!)$ induced by $\mathbb Q\to L$. The assertion is: if a Laurent series $x$ over $L$ lies in $\mathrm{laurentBaseChange}\,L$ of $\mathrm{xHFunctionField}(\ell'^{2}M')(\mathrm{levelH}\,\ell'\,M')$, then its image under [`ModularCurve.qExpand L q`](def/ModularCurve_X0.html#L25), the ring endomorphism of $L(\!(\mathsf q)\!)$ multiplying all exponents by $q$ (that is, $x\mapsto x(\mathsf q^{q})$), lies in $\mathrm{laurentBaseChange}\,L$ of $\mathrm{xHFunctionField}((q\ell')^{2}M')(\mathrm{levelH}\,(q\ell')\,M')$.
--
--   This is the function-field effect of the degeneracy map $\tau\mapsto q\tau$: substituting $\mathsf q^{q}$ for $\mathsf q$ carries the field of $\mathsf q$-expansions of level $\ell'^{2}M'$ with diamond condition modulo $\ell'$ into the corresponding field of level $(q\ell')^{2}M'$ with diamond condition modulo $q\ell'$, after base change of coefficients to $L$. It is used in the analysis of the chart algebras `chartAlgFin` at supersingular points, in [`ModularCurve.FullLevel.eq_of_isMaximal_of_mem_ssJSet_of_forall_coe_eq_qExpand_iff_chartAlgFin`](thm.html#ModularCurve.FullLevel.eq_of_isMaximal_of_mem_ssJSet_of_forall_coe_eq_qExpand_iff_chartAlgFin) and [`ModularCurve.FullLevel.mem_of_coe_mem_nonunits_of_isMaximal_of_mem_ssJSet_chartAlgFin`](thm.html#ModularCurve.FullLevel.mem_of_coe_mem_nonunits_of_isMaximal_of_mem_ssJSet_chartAlgFin).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_qExpand_mem_laurentBaseChange_xHFunctionField_levelH_mul_of_mem.lean

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.FullLevel.qExpand_mem_laurentBaseChange_xHFunctionField_levelH_mul_of_mem
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (ℓ' : ℕ) [Fact ℓ'.Prime]
    (L : Type) [Field L] [CharZero L]
    (x : LaurentSeries L)
    (hx : x ∈ ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (ℓ' ^ 2 * M') (ModularCurve.FullLevel.levelH ℓ' M'))) :
    ModularCurve.qExpand L q x ∈
      ModularCurve.laurentBaseChange L
        (ModularCurve.xHFunctionField ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M')) := by sorry
