-- Prove2me | Theorems.Thm_Module_Finite_of_ker_le_range_of_isNoetherianRing
-- name    : Module.Finite.of_ker_le_range_of_isNoetherianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/d6f94ad1-12b0-5b05-87fd-000d72f72d7c
-- title:
--   Finiteness sandwich over a Noetherian ring
-- statement:
--   Let $R$ be a commutative Noetherian ring and let $M$, $N_1$, $N_2$ be $R$-modules (abelian groups with $R$-module structures) such that $N_1$ and $N_2$ are finitely generated over $R$. Given $R$-linear maps $\alpha : N_1 \to M$ and $\beta : M \to N_2$ with the inclusion $\ker \beta \le \operatorname{range} \alpha$ of submodules of $M$, the conclusion is that $M$ is a finitely generated $R$-module. No exactness at $M$ is assumed beyond the stated one-sided inclusion (the reverse inclusion $\operatorname{range}\alpha \le \ker\beta$, i.e. $\beta \circ \alpha = 0$, is not required), and neither $\alpha$ nor $\beta$ is assumed injective or surjective.
--
--   This is the elementary finiteness transfer underlying the "two out of three" principle for finiteness along exact sequences over a Noetherian base. It is used by the Čech-cohomology finiteness statements [`AlgebraicGeometry.OModulePresheaf.cechFinite_of_affSES_left`](thm.html#AlgebraicGeometry.OModulePresheaf.cechFinite_of_affSES_left), `...cechFinite_of_affSES_mid` and `...cechFinite_of_affSES_right`, where finiteness of one term of a short exact sequence of modules is deduced from that of the other two.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_Finite_of_ker_le_range_of_isNoetherianRing.lean

import Mathlib.RingTheory.Noetherian.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Module.Finite.of_ker_le_range_of_isNoetherianRing {R : Type*} [CommRing R] [IsNoetherianRing R] {M N₁ N₂ : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂] [Module.Finite R N₁] [Module.Finite R N₂] (α : N₁ →ₗ[R] M) (β : M →ₗ[R] N₂) (h : LinearMap.ker β ≤ LinearMap.range α) : Module.Finite R M := by sorry
