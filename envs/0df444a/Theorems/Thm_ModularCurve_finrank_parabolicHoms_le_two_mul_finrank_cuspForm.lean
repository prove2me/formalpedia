-- Prove2me | Theorems.Thm_ModularCurve_finrank_parabolicHoms_le_two_mul_finrank_cuspForm
-- name    : ModularCurve.finrank_parabolicHoms_le_two_mul_finrank_cuspForm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/d108d922-7cc0-5a6b-84c9-dc781392805e
-- title:
--   dim_ℝH¹ₚₐᵣ(Γ₀(N),ℝ)≤ 2dim_ℂS₂(Γ₀(N))
-- statement:
--   Let $N$ be a natural number, assumed nonzero. Consider the congruence subgroup $\Gamma_0(N)\le \mathrm{SL}_2(\mathbb Z)$ and, inside the additive group of all additive-group homomorphisms from the additive copy of $\Gamma_0(N)$ to $\mathbb R$, the real submodule [`ModularCurve.Period.parabolicHoms`](def/ModularCurve_PeriodMap.html#L62) of those homomorphisms $\varphi$ that are parabolic in the sense of the project's predicate `IsParabolicHom`: for every $\gamma\in\Gamma_0(N)$ whose underlying integer $2\times 2$ matrix satisfies $(\operatorname{tr}\gamma)^2=4$, one has $\varphi(\gamma)=0$ (the group law of $\Gamma_0(N)$ being written additively). On the other side, let $S_2(\Gamma_0(N))$ be the space `CuspForm (CongruenceSubgroup.Gamma0 N) 2` of weight-two cusp forms for $\Gamma_0(N)$, a complex vector space. The assertion is the inequality of Mathlib ranks $$\operatorname{finrank}_{\mathbb R}\big(\text{parabolic homomorphisms }\Gamma_0(N)\to\mathbb R\big)\ \le\ 2\cdot \operatorname{finrank}_{\mathbb C} S_2(\Gamma_0(N)),$$ an inequality of natural numbers, with `Module.finrank` taken in the usual Mathlib convention.
--
--   This is the dimension-counting half of the real Eichler–Shimura correspondence for $\Gamma_0(N)$ in weight two: the space of real parabolic characters of $\Gamma_0(N)$ is no larger than twice the space of weight-two cusp forms, both sides classically being $2g$ with $g$ the genus of $X_0(N)$. It feeds the construction of period lattices and the Abel–Jacobi/period dictionary for modular curves, in particular the statements producing bases of the period lattice and cusp forms with prescribed period behaviour.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finrank_parabolicHoms_le_two_mul_finrank_cuspForm.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.finrank_parabolicHoms_le_two_mul_finrank_cuspForm (N : ℕ) [NeZero N] :
    Module.finrank ℝ (ModularCurve.Period.parabolicHoms ℝ (CongruenceSubgroup.Gamma0 N) ℝ) ≤
      2 * Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) := by sorry
