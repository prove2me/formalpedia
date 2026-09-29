-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_eval_gl2Jac_scalarElem_eq_diamondHBar_inv_eval_pow
-- name    : ModularCurve.FullLevel.eval_gl2Jac_scalarElem_eq_diamondHBar_inv_eval_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/5ef6f658-4f0b-54ce-bce6-e8529e9757e4
-- title:
--   Scalars act by inverse diamond and squared component shift
-- statement:
--   Fix a prime $q$ and a nonzero natural number $M'$, and assume the hypothesis `GL2Laws q M'`: there exists a monoid homomorphism $G$ from $\mathrm{GL}_2(\mathbb{Z}/q)$ to the additive endomorphisms of $\mathrm{Jac}(q,M')$ such that $G$ of the mod-$q$ reduction of any $\gamma \in \Gamma_0(M')$ is the operator `slJac q M' γ`, and $G$ of the matrix $\mathrm{diag}(1,e)$ is `diagJac q M' e` for every unit $e$ of $\mathbb{Z}/q$; `gl2Jac q M'` denotes such a homomorphism (and the trivial one otherwise). Here $\mathrm{Jac}(q,M')$ is the group of functions from $\mathrm{Idx}(q)$, the set of primitive $q$-th roots of unity in $\overline{\mathbb{Q}}$, to $J_H(q^2M')$, where $H$ is the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$. Let $d$ be a natural number coprime to $q$ and coprime to $q^2M'$, let $x \in \mathrm{Jac}(q,M')$ and let $\zeta$ be a primitive $q$-th root of unity. Then the value at $\zeta$ of $\mathrm{gl2Jac}(d\cdot I)\,x$, where $d \cdot I$ is the scalar matrix attached to the unit $d$ of $\mathbb{Z}/q$, equals the diamond endomorphism `diamondHBar` of $J_H(q^2M')$ at the inverse of the class of $d$ in $(\mathbb{Z}/q^2M')^\times$, applied to the value of $x$ at the root of unity $\zeta$ raised to the canonical representative of $(d^2)^{-1}$ in $\mathbb{Z}/q$.
--
--   This records the action of the centre of $\mathrm{GL}_2(\mathbb{F}_q)$ on the Jacobian of the modular curve of full level $q$ with $\Gamma_0(M')$-structure, in the coordinates given by the decomposition into geometric components indexed by primitive $q$-th roots of unity: a scalar $d$ permutes the components by $\zeta \mapsto \zeta^{d^2}$ and acts inside a component by the diamond operator of $d^{-1}$. It feeds the Tate-module formulation of the Eichler–Shimura congruence relation at full level, being used by [`ModularCurve.FullLevel.tateGal_mul_tateGal_sub_tateHecke_mul_tateGal_add_smul_tateGL2_scalarElem_eq_zero`](thm.html#ModularCurve.FullLevel.tateGal_mul_tateGal_sub_tateHecke_mul_tateGal_add_smul_tateGL2_scalarElem_eq_zero) and [`ModularCurve.FullLevel.tateHecke_mul_tateGL2_comm`](thm.html#ModularCurve.FullLevel.tateHecke_mul_tateGL2_comm).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_eval_gl2Jac_scalarElem_eq_diamondHBar_inv_eval_pow.lean

import Definitions.Def_ModularCurve_FullLevelJacobian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve.FullLevel
open ModularCurve

theorem ModularCurve.FullLevel.eval_gl2Jac_scalarElem_eq_diamondHBar_inv_eval_pow
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hG : ModularCurve.FullLevel.GL2Laws q M')
    (d : ℕ) (hdq : d.Coprime q) (hd : d.Coprime (q ^ 2 * M'))
    (x : ModularCurve.FullLevel.Jac q M') (ζ : ModularCurve.FullLevel.Idx q) :
    (ModularCurve.FullLevel.gl2Jac q M' (CuspidalType.scalarElem q (ZMod.unitOfCoprime d hdq)) x).eval ζ =
      ModularCurve.diamondHBar (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')
        (ZMod.unitOfCoprime d hd)⁻¹
        (x.eval (ζ.pow ((ZMod.unitOfCoprime d hdq) ^ 2)⁻¹)) := by sorry
