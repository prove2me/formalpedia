-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_mul_card_ge_of_forall_levelAutBar_mem
-- name    : ModularCurve.FullLevel.mul_card_ge_of_forall_levelAutBar_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/e4ede130-5a79-519a-a9be-55fc2f17c4f2
-- title:
--   Lower bound q(q²-1)≤ 2|G| for level automorphism groups
-- statement:
--   Let $q$ be a prime with $q\ge 5$, let $M'$ be a nonzero natural number with $q\nmid M'$, and let $\zeta$ be an element of `Idx q`, i.e. a primitive $q$-th root of unity in $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`. Write $F =$ `fieldBar q M'` for the compositum of $\overline{\mathbb{Q}}$ with the function field `xHFunctionField (q ^ 2 * M') (levelH q M')` inside the Laurent series field $\overline{\mathbb{Q}}((X))$, where `levelH q M'` is the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$. For $\gamma \in \mathrm{SL}_2(\mathbb{Z})$, `levelAutBar q M' ζ γ` denotes the automorphism of $F$ over $\overline{\mathbb{Q}}$ selected by the predicate `IsLevelAutBar q M' ζ γ`, which requires that for every weight $k$, every pair $f,g$ of modular forms of weight $k$ on $\Gamma_H(q^2M')$ with integral $q$-expansions $p_f,p_g$, $p_g$ having nonzero associated series, and every embedding $\iota:\overline{\mathbb{Q}}\to\mathbb{C}$ with $\iota(\zeta)=e^{2\pi i/q}$, the $\iota$-image of the value of the automorphism on the ratio of the $q$-expansions of $f$ and $g$ equals the ratio of the $q$-expansions of $f$ and $g$ translated by `conjElem q γ` (the identity automorphism being taken when no such $\tau$ exists). Let $G$ be a finite subgroup of $\mathrm{Aut}_{\overline{\mathbb{Q}}}(F)$ such that `levelAutBar q M' ζ γ` lies in $G$ for every $\gamma\in\Gamma_0(M')$. Then $q(q^2-1)\le 2\,|G|$.
--
--   This records the near-faithfulness of the map $\gamma\mapsto$ `levelAutBar q M' ζ γ` on $\Gamma_0(M')$: any finite group of $\overline{\mathbb{Q}}$-automorphisms of the full-level modular function field containing all these level automorphisms has order at least $|\mathrm{PSL}_2(\mathbb{F}_q)| = q(q^2-1)/2$, the surjectivity of $\Gamma_0(M')\to \mathrm{SL}_2(\mathbb{F}_q)$ for $q\nmid M'$ and the Igusa valuation rings of $q$-expansions being the inputs. It is used in the identification of elements of $F$ fixed by all level automorphisms with $q$-expansions, [`ModularCurve.FullLevel.exists_coe_eq_qExpand_of_forall_levelAutBar_apply_eq`](thm.html#ModularCurve.FullLevel.exists_coe_eq_qExpand_of_forall_levelAutBar_apply_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_mul_card_ge_of_forall_levelAutBar_mem.lean

import Definitions.Def_ModularCurve_FullLevelJacobian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve CongruenceSubgroup
open ModularCurve.FullLevel
open scoped MatrixGroups

theorem ModularCurve.FullLevel.mul_card_ge_of_forall_levelAutBar_mem
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (ζ : Idx q)
    (G : Subgroup (fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] fieldBar q M')) [Finite ↥G]
    (hG : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M' → levelAutBar q M' ζ γ ∈ G) :
    q * (q ^ 2 - 1) ≤ 2 * Nat.card ↥G := by sorry
