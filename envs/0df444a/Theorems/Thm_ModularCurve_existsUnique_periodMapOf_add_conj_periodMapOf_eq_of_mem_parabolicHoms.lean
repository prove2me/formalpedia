-- Prove2me | Theorems.Thm_ModularCurve_existsUnique_periodMapOf_add_conj_periodMapOf_eq_of_mem_parabolicHoms
-- name    : ModularCurve.existsUnique_periodMapOf_add_conj_periodMapOf_eq_of_mem_parabolicHoms
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/0637231d-c371-596c-baeb-3f3da9715c6d
-- title:
--   Eichler–Shimura: parabolic characters as sums of periods
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb{Z})$ satisfying `CongruenceSubgroup.IsCongruenceSubgroup`, and let $\varphi$ be a homomorphism from $\Gamma$ (written additively via `Additive`) to the additive group $\mathbb{C}$ which lies in the submodule [`ModularCurve.Period.parabolicHoms ℂ Γ ℂ`](def/ModularCurve_PeriodMap.html#L62), that is, $\varphi(\gamma)=0$ for every $\gamma\in\Gamma$ whose underlying integral matrix satisfies $(\operatorname{tr}\gamma)^2=4$. The assertion is that there is exactly one pair $(f,g)$ of cusp forms of weight $2$ for $\Gamma$ with
--   $$\mathrm{periodMapOf}\,\Gamma\,f \;+\; \overline{\mathrm{periodMapOf}\,\Gamma\,g} \;=\; \varphi$$
--   as homomorphisms $\Gamma\to(\mathbb{C},+)$, the second summand being the composite of $\mathrm{periodMapOf}\,\Gamma\,g$ with complex conjugation (`starRingEnd ℂ`). Here [`ModularCurve.periodMapOf Γ f`](def/ModularCurve_PeriodOf.html#L79) is the period homomorphism attached to $f$: if there exists $F:\mathbb{H}\to\mathbb{C}$ with $F'=f$ on the upper half-plane, with $F\to 0$ at $i\infty$, with $F$ an equivariant primitive for $\Gamma$ in the sense of `Period.IsEquivariantPrimitive`, and such that $F(\delta\cdot w)$ has a limit at $i\infty$ for every $\delta\in\mathrm{SL}_2(\mathbb{Z})$, then it is the homomorphism $\gamma\mapsto$ period of such an $F$ along $\gamma$, and it is the zero homomorphism otherwise.
--
--   This is the Eichler–Shimura isomorphism in weight $2$, in the form that the real-linear map $S_2(\Gamma)\oplus\overline{S_2(\Gamma)}\to H^1_{\mathrm{par}}(\Gamma,\mathbb{C})$, $(f,g)\mapsto \operatorname{per}f+\overline{\operatorname{per}g}$, is bijective. It is used to produce a weight-$2$ cusp form, and then a Hecke eigenform with prescribed $q$-expansion coefficients, out of a parabolic homomorphism that is an eigenvector for the Hecke operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_existsUnique_periodMapOf_add_conj_periodMapOf_eq_of_mem_parabolicHoms.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.existsUnique_periodMapOf_add_conj_periodMapOf_eq_of_mem_parabolicHoms
    (Γ : Subgroup SL(2, ℤ)) (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ)
    (φ : Additive Γ →+ ℂ) (hφ : φ ∈ ModularCurve.Period.parabolicHoms ℂ Γ ℂ) :
    ∃! fg : CuspForm Γ 2 × CuspForm Γ 2,
      ModularCurve.periodMapOf Γ fg.1 +
        (starRingEnd ℂ).toAddMonoidHom.comp (ModularCurve.periodMapOf Γ fg.2) = φ := by sorry
