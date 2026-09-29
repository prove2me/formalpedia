-- Prove2me | Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_ramification_eq_one_gamma1
-- name    : ModularCurve.ComplexPlaceDictionaryOf.ramification_eq_one_gamma1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/906fd3d2-fdfb-5dfe-971b-91dfcbd89604
-- title:
--   Ramification index one for Γ₁(M), M ≥ 4
-- statement:
--   Fix a natural number $M$ with $M \neq 0$ and $4 \le M$, and let $F_0$ be an intermediate field of $\mathbb{Q} \subseteq \mathbb{Q}((q))$ which is assumed equal to [`ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M)`](def/ModularCurve_X1.html#L101), that is, to the subfield of the Laurent series field generated over $\mathbb{Q}$ by all quotients $\mathrm{intSeriesC}\,p_f / \mathrm{intSeriesC}\,p_g$ arising from modular forms $f,g$ of a common weight $k$ for $\Gamma_1(M)$ together with integral $q$-expansions $p_f, p_g \in \mathbb{Z}[[q]]$ of them, the denominator series being nonzero. Let $D$ be a complex place dictionary for $(\Gamma_1(M), F_0)$: a datum consisting of a map $\mathrm{pt}$ from the upper half-plane $\mathbb{H}$ to the places of the field $\mathbb{C} \cdot F_0 \subseteq \mathbb{C}((q))$ obtained by adjoining to $\mathbb{C}$ the coefficientwise image of $F_0$ (a place being a proper valuation subring containing the base field whose ring is a principal ideal ring), a map $\mathrm{ramification} : \mathbb{H} \to \mathbb{N}$ with strictly positive values, invariance $\mathrm{pt}(\gamma \cdot \tau) = \mathrm{pt}(\tau)$ for $\gamma \in \Gamma_1(M)$, the requirement that $x$ lie in the valuation subring of $\mathrm{pt}(\tau)$ exactly when $z \mapsto \lVert \mathrm{realizeOf}\,x\,z \rVert$ is bounded on a punctured neighbourhood of $\tau$, and the requirement that for every nonzero $x$ the meromorphic order at $\tau$ of the function $z \mapsto \mathrm{realizeOf}\,x\,z$ equal $\mathrm{ramification}(\tau) \cdot \mathrm{ord}_{\mathrm{pt}(\tau)}(x)$; here $\mathrm{realizeOf}\,x\,\tau$ is $g(\tau)/h(\tau)$ for some choice of modular forms $g,h$ of equal weight for the group with $h(\tau) \neq 0$ and $x \cdot q\text{-exp}(h) = q\text{-exp}(g)$, and $0$ if no such pair exists. Then for every $\tau \in \mathbb{H}$ one has $\mathrm{ramification}(\tau) = 1$.
--
--   This is the statement that $\Gamma_1(M)$ has no elliptic points for $M \ge 4$, in the form needed for the dictionary between points of the upper half-plane and places of the function field of $X_1(M)$: the analytic order of vanishing of a realized function at $\tau$ agrees with its valuation at the corresponding place, with no multiplier. It is used in the comparison of valuations with weights at such places, via [`ModularCurve.even_ord_add_weightFloor_of_mem_toValuationSubring_laurentBaseChange_gamma1`](thm.html#ModularCurve.even_ord_add_weightFloor_of_mem_toValuationSubring_laurentBaseChange_gamma1).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ComplexPlaceDictionaryOf_ramification_eq_one_gamma1.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.ComplexPlaceDictionaryOf.ramification_eq_one_gamma1
    (M : ℕ) [NeZero M] (hM : 4 ≤ M)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (hF : F₀ = ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))
    (D : ModularCurve.ComplexPlaceDictionaryOf (CongruenceSubgroup.Gamma1 M) F₀) (τ : UpperHalfPlane) :
    D.ramification τ = 1 := by sorry
