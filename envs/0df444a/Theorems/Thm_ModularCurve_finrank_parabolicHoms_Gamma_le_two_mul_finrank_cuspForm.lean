-- Prove2me | Theorems.Thm_ModularCurve_finrank_parabolicHoms_Gamma_le_two_mul_finrank_cuspForm
-- name    : ModularCurve.finrank_parabolicHoms_Gamma_le_two_mul_finrank_cuspForm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/a7cf4047-296d-5cea-b157-7b0a64c09e9c
-- title:
--   Rank of parabolic homomorphisms of Γ(N) bounded by 2dim S₂
-- statement:
--   Let $N$ be a natural number, assumed nonzero. Inside the additive group of group homomorphisms $\mathrm{Additive}(\Gamma(N)) \to \mathbb{Z}$, where $\Gamma(N) \le \mathrm{SL}_2(\mathbb{Z})$ is the principal congruence subgroup of level $N$ and $\mathrm{Additive}$ turns its multiplicative group structure into an additive one, consider the $\mathbb{Z}$-submodule [`ModularCurve.Period.parabolicHoms`](def/ModularCurve_PeriodMap.html#L62) consisting of those $\varphi$ that satisfy the predicate `IsParabolicHom`: $\varphi(\gamma) = 0$ for every $\gamma \in \Gamma(N)$ whose underlying $2 \times 2$ integer matrix has trace with square equal to $4$, i.e. trace $\pm 2$. The theorem asserts the inequality of natural numbers $$\operatorname{finrank}_{\mathbb{Z}} \big(\mathrm{parabolicHoms}\,\mathbb{Z}\,\Gamma(N)\,\mathbb{Z}\big) \le 2 \cdot \operatorname{finrank}_{\mathbb{C}} \mathrm{CuspForm}(\Gamma(N), 2),$$ where the right-hand side is twice the complex dimension of the space of weight-$2$ cusp forms for $\Gamma(N)$. Both ranks are the Mathlib `Module.finrank`, hence natural numbers, and the inequality is one of natural numbers.
--
--   This is the inequality expressing the surjectivity half of the Eichler–Shimura relation at principal level: the rank of the group of parabolic (trace $\pm 2$ killing) homomorphisms $\Gamma(N) \to \mathbb{Z}$ is at most twice $\dim_{\mathbb{C}} S_2(\Gamma(N))$. It is the input from which the corresponding bound for an arbitrary congruence subgroup is obtained by descent, in [`ModularCurve.finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup`](thm.html#ModularCurve.finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finrank_parabolicHoms_Gamma_le_two_mul_finrank_cuspForm.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.finrank_parabolicHoms_Gamma_le_two_mul_finrank_cuspForm (N : ℕ) [NeZero N] :
    Module.finrank ℤ (ModularCurve.Period.parabolicHoms ℤ (CongruenceSubgroup.Gamma N) ℤ) ≤
      2 * Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma N) 2) := by sorry
