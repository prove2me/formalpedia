-- Prove2me | Theorems.Thm_ModularCurve_periodMapOf_mem_parabolicHoms
-- name    : ModularCurve.periodMapOf_mem_parabolicHoms
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/ac48d659-8a40-5df1-96e7-159faa0089b4
-- title:
--   Period maps of weight-2 cusp forms are parabolic
-- statement:
--   Let $\Gamma$ be an arbitrary subgroup of $\mathrm{SL}_2(\mathbb{Z})$ and let $f$ be a cusp form of weight $2$ for $\Gamma$. The assertion is that the additive homomorphism $\mathrm{periodMapOf}\ \Gamma\ f : \mathrm{Additive}\ \Gamma \to_{+} \mathbb{C}$ belongs to the submodule [`ModularCurve.Period.parabolicHoms ℂ Γ ℂ`](def/ModularCurve_PeriodMap.html#L62) of $\mathbb{C}$-valued additive characters of $\Gamma$, that is, it satisfies `IsParabolicHom`: $\varphi(\gamma) = 0$ for every $\gamma \in \Gamma$ whose underlying integral matrix has $(\operatorname{tr}\gamma)^2 = 4$, i.e. trace $\pm 2$. Here $\mathrm{periodMapOf}\ \Gamma\ f$ is defined by cases: if there exists $F : \mathbb{H} \to \mathbb{C}$ satisfying `HasEquivariantPrimitiveOf Γ f F` — namely $F \circ \mathrm{ofComplex}$ has derivative $f(\tau)$ at every $\tau \in \mathbb{H}$, $F \to 0$ as $\operatorname{Im} \to \infty$, $F$ satisfies the predicate `Period.IsEquivariantPrimitive Γ F`, whose attached function $\mathrm{period}$ assigns to $\gamma \in \Gamma$ the value $F(\gamma \cdot z) - F(z)$ independently of $z$ and is additive in $\gamma$, and for each $\delta \in \mathrm{SL}_2(\mathbb{Z})$ the function $w \mapsto F(\delta \cdot w)$ has a limit along $\operatorname{Im} w \to \infty$ — then it is the character $\gamma \mapsto \mathrm{period}\ \gamma$ attached to such an $F$; otherwise it is the zero homomorphism. No hypothesis guaranteeing the existence of such an $F$ is imposed, so the degenerate case is covered trivially.
--
--   This is the statement that the period character of a weight-$2$ cusp form is parabolic, i.e. kills the stabilisers of the cusps, so that the period map lands in the parabolic part $H^1_{\mathrm{par}}(\Gamma,\mathbb{C})$ of $H^1(\Gamma,\mathbb{C})$. It feeds the Eichler–Shimura-type comparison between weight-$2$ cusp forms and parabolic cohomology used later for Hecke eigenform and Galois-module constructions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_periodMapOf_mem_parabolicHoms.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.periodMapOf_mem_parabolicHoms (Γ : Subgroup SL(2, ℤ)) (f : CuspForm Γ 2) :
    ModularCurve.periodMapOf Γ f ∈ ModularCurve.Period.parabolicHoms ℂ Γ ℂ := by sorry
