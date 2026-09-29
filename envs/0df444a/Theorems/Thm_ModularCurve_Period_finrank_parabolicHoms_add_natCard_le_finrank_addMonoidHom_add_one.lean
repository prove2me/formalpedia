-- Prove2me | Theorems.Thm_ModularCurve_Period_finrank_parabolicHoms_add_natCard_le_finrank_addMonoidHom_add_one
-- name    : ModularCurve.Period.finrank_parabolicHoms_add_natCard_le_finrank_addMonoidHom_add_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/0f90f902-6270-5272-a743-919daad53e1d
-- title:
--   Parabolic characters plus cusp count bounded by dimHom(Γ,K)+1
-- statement:
--   Let $\Gamma$ be a subgroup of finite index in $\mathrm{SL}_2(\mathbb{Z})$ containing $-1$, and let $K$ be a field. Consider the $K$-vector space $\mathrm{Hom}(\Gamma,K)$ of additive group homomorphisms from the additive group underlying $\Gamma$ (that is, `Additive Γ`) to $K$, and inside it the subspace [`ModularCurve.Period.parabolicHoms K Γ K`](def/ModularCurve_PeriodMap.html#L62) consisting of those $\varphi$ with $\varphi(\gamma)=0$ for every $\gamma\in\Gamma$ whose image in $M_2(\mathbb{Z})$ has $(\operatorname{tr}\gamma)^2=4$, i.e. trace $\pm 2$. Let the cusp set be the quotient of $\mathrm{SL}_2(\mathbb{Z})/\Gamma$ by the orbit equivalence relation for the action of the cyclic group $\langle T\rangle$ of integer powers of $T=\begin{pmatrix}1&1\\0&1\end{pmatrix}$, and let its cardinality be measured by `Nat.card`. The assertion is the numerical inequality
--   $$\dim_K \big(\text{parabolic homomorphisms}\big) + \#\big(\langle T\rangle\text{-orbits on }\mathrm{SL}_2(\mathbb{Z})/\Gamma\big) \le \dim_K \mathrm{Hom}(\Gamma,K) + 1,$$
--   the dimensions being Mathlib's `Module.finrank`.
--
--   This is the standard dimension count comparing parabolic cohomology in degree one with the full character space of $\Gamma$, the discrepancy being governed by the number of cusps: the evaluation of a character on the cusp generators covers the hyperplane of sum-zero functions on the cusps. It is used in the project's computations of $\dim_K H^1_{\mathrm{par}}$ for $\Gamma_0(N)$ and $\Gamma(N)$, namely in [`ModularCurve.finrank_parabolicHoms_gamma0_le_two_mul_genusFormula`](thm.html#ModularCurve.finrank_parabolicHoms_gamma0_le_two_mul_genusFormula) and [`ModularCurve.six_mul_level_mul_finrank_parabolicHoms_Gamma_add_eq`](thm.html#ModularCurve.six_mul_level_mul_finrank_parabolicHoms_Gamma_add_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_Period_finrank_parabolicHoms_add_natCard_le_finrank_addMonoidHom_add_one.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.Period.finrank_parabolicHoms_add_natCard_le_finrank_addMonoidHom_add_one
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Γ) (K : Type) [Field K] :
    Module.finrank K (ModularCurve.Period.parabolicHoms K Γ K)
      + Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers ModularGroup.T)
          (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ Γ))
      ≤ Module.finrank K (Additive Γ →+ K) + 1 := by sorry
