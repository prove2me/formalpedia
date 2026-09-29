-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_mul_card_ge_of_forall_levelAutBar_mem_of_eq_two
-- name    : ModularCurve.FullLevel.mul_card_ge_of_forall_levelAutBar_mem_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/808d8ff3-6be1-532b-bdd0-9e028485a4ba
-- title:
--   Order bound q(q²-1)≤|G| for level automorphisms at q=2
-- statement:
--   Let $q$ be a prime with $q=2$, let $M'\ge 1$ be an integer with $q\nmid M'$, and let $H=$ `levelH q M'` be the kernel of the reduction map $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$, i.e. the units congruent to $1$ modulo $q$. Write $F=$ `fieldBar q M'` for the base change to $\overline{\mathbb{Q}}$ of the function field `xHFunctionField (q^2*M') H`, realised as an intermediate field of the Laurent series field $\overline{\mathbb{Q}}((X))$ over $\overline{\mathbb{Q}}$. Fix $\zeta$ a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$, and let $G$ be a finite subgroup of the group of $\overline{\mathbb{Q}}$-algebra automorphisms of $F$. Assume that for every $\gamma\in\mathrm{SL}_2(\mathbb{Z})$ lying in $\Gamma_0(M')$ the automorphism `levelAutBar q M' ζ γ` belongs to $G$; here `levelAutBar q M' ζ γ` is a chosen automorphism $\tau$ of $F$ satisfying `IsLevelAutBar`, namely that for all weights $k$, all modular forms $f,g$ of weight $k$ for $\Gamma_H(q^2M')$ with integral $q$-expansions $p_f,p_g$ and $p_g$ having nonzero associated series, and every embedding $\iota:\overline{\mathbb{Q}}\to\mathbb{C}$ with $\iota(\zeta)=e^{2\pi i/q}$, the series $\iota(\tau(f/g))$ times the $q$-expansion of $g\mid_k \mathrm{conjElem}(q,\gamma)$ equals the $q$-expansion of $f\mid_k \mathrm{conjElem}(q,\gamma)$ (and the identity automorphism if no such $\tau$ exists). The conclusion is $q(q^2-1)\le \#G$.
--
--   This is the order estimate expressing that the level automorphisms attached to $\Gamma_0(M')$ realise $\mathrm{SL}_2(\mathbb{F}_q)$ inside $\mathrm{Aut}_{\overline{\mathbb{Q}}}(F)$; for $q=2$ the map is faithful because $-I\in\Gamma(2)$, so the bound has no factor $2$, in contrast with the odd-$q$ versions where only $\mathrm{PSL}_2(\mathbb{F}_q)$ is obtained. It feeds the fixed-field argument in [`ModularCurve.FullLevel.exists_coe_eq_qExpand_of_forall_levelAutBar_apply_eq_of_eq_two`](thm.html#ModularCurve.FullLevel.exists_coe_eq_qExpand_of_forall_levelAutBar_apply_eq_of_eq_two), where a subgroup fixing a given function must be compared with the full level-automorphism group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_mul_card_ge_of_forall_levelAutBar_mem_of_eq_two.lean

import Definitions.Def_ModularCurve_FullLevelJacobian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel CongruenceSubgroup
open scoped MatrixGroups

theorem ModularCurve.FullLevel.mul_card_ge_of_forall_levelAutBar_mem_of_eq_two
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (ζ : Idx q)
    (G : Subgroup (fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] fieldBar q M')) [Finite ↥G]
    (hG : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M' → levelAutBar q M' ζ γ ∈ G) :
    q * (q ^ 2 - 1) ≤ Nat.card ↥G := by sorry
