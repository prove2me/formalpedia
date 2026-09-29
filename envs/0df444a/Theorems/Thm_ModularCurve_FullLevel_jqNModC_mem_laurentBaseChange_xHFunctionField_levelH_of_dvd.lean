-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_jqNModC_mem_laurentBaseChange_xHFunctionField_levelH_of_dvd
-- name    : ModularCurve.FullLevel.jqNModC_mem_laurentBaseChange_xHFunctionField_levelH_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/b3f95ce8-c6f9-5a0f-9df2-e2df2fa60a1e
-- title:
--   j(mathsf q^N) lies in the base-changed Γ_H expansion field
-- statement:
--   Let $q$ and $\ell'$ be primes, let $M'\ge 1$, let $L$ be a field of characteristic $0$, and let $N\ge 1$ satisfy $N \mid (q\ell')^2 M'$. Write $H =$ [`ModularCurve.FullLevel.levelH (q*ℓ') M'`](def/ModularCurve_FullLevelJacobian.html#L22) for the kernel of the reduction homomorphism $(\mathbb{Z}/(q\ell')^2M')^\times \to (\mathbb{Z}/q\ell')^\times$, i.e. the units congruent to $1$ modulo $q\ell'$, and let `xHFunctionField ((q*ℓ')^2*M') H` be the intermediate field of $\mathbb{Q}((\mathsf q))$ produced by `xHFunctionFieldC` from the congruence-subgroup datum [`CohCarrier.GammaH`](def/CohCarrier_Level.html#L133) at level $(q\ell')^2M'$ and subgroup $H$. The element `jqNModC L N` is $\mathsf q \mapsto \mathsf q^N$ applied to the $q$-expansion of $j$ over $L$: the Laurent series `jqModC L` $= \mathsf q^{-1}\cdot$ (the image in $L$ of the integral power series `jNum`) is pushed forward by the exponent-scaling ring homomorphism `qExpand L N`, which multiplies all exponents by $N$. The assertion is that this element lies in `laurentBaseChange L (xHFunctionField ((q*ℓ')^2*M') H)`, the intermediate field of $L((\mathsf q))$ generated over $L$ by the coefficientwise image of that rational expansion field under $\mathbb{Q}\to L$.
--
--   Classically this is the statement that $z \mapsto j(Nz)$ is a modular function for $\Gamma_0(N) \supseteq \Gamma_H((q\ell')^2M')$ with rational $q$-expansion coefficients, so that its expansion survives base change to $L$; it supplies a concrete element of the full-level function field at level $(q\ell')^2M'$. It is used in the analysis of level automorphisms and Tate points on the full-level modular curve, in [`ModularCurve.FullLevel.AuxLevel.isMaximal_comap_restrict_and_mem_ssJSet_of_isLevelAutAt`](thm.html#ModularCurve.FullLevel.AuxLevel.isMaximal_comap_restrict_and_mem_ssJSet_of_isLevelAutAt) and in [`ModularCurve.FullLevel.apply_eq_cyclicQuotientJ_pow_of_levelAut_of_originChart_of_forall_nsmul_eq_zero_of_tatePoint`](thm.html#ModularCurve.FullLevel.apply_eq_cyclicQuotientJ_pow_of_levelAut_of_originChart_of_forall_nsmul_eq_zero_of_tatePoint).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_jqNModC_mem_laurentBaseChange_xHFunctionField_levelH_of_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_FullLevelJacobian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.FullLevel.jqNModC_mem_laurentBaseChange_xHFunctionField_levelH_of_dvd
    (q : ℕ) [Fact q.Prime] (ℓ' : ℕ) [Fact ℓ'.Prime] (M' : ℕ) [NeZero M']
    (L : Type) [Field L] [CharZero L]
    (N : ℕ) [NeZero N] (hN : N ∣ (q * ℓ') ^ 2 * M') :
    ModularCurve.jqNModC L N ∈
      ModularCurve.laurentBaseChange L
        (ModularCurve.xHFunctionField ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M')) := by sorry
