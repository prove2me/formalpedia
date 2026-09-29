-- Prove2me | Theorems.Thm_ModularCurve_periodMap_injective
-- name    : ModularCurve.periodMap_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/44148d26-b89a-5f96-972b-2d01933237e0
-- title:
--   Injectivity of the period map on weight-2 cusp forms
-- statement:
--   Let $N$ be a natural number with $N \neq 0$. The assertion is that the map [`ModularCurve.periodMap N`](def/ModularCurve_PeriodMapBundled.html#L20) is injective as a function from the space of cusp forms of weight $2$ for $\Gamma_0(N)$ to the additive homomorphisms $\mathrm{Additive}(\Gamma_0(N)) \to \mathbb{C}$, where $\Gamma_0(N)$ is viewed as a subgroup of $SL(2,\mathbb{Z})$ and $\mathrm{Additive}$ is its underlying group written additively. By definition, [`ModularCurve.periodMap N f`](def/ModularCurve_PeriodMapBundled.html#L20) is obtained by cases: if there exists $F : \mathbb{H} \to \mathbb{C}$ satisfying `HasEquivariantPrimitive N f F`, that is, $F \circ \mathrm{ofComplex}$ has derivative $f(\tau)$ at each $\tau \in \mathbb{H}$, $F$ tends to $0$ along the filter `atImInfty`, $F$ satisfies the predicate `IsEquivariantPrimitive` for $\Gamma_0(N)$, and for every $\delta \in SL(2,\mathbb{Z})$ the function $w \mapsto F(\delta \cdot w)$ has a limit along `atImInfty`, then `periodMap N f` is the period homomorphism `periodHom` attached to a chosen such $F$, namely $\gamma \mapsto \mathrm{period}(\gamma)$ regarded as an additive homomorphism; otherwise it is the zero homomorphism. Thus two weight-2 cusp forms for $\Gamma_0(N)$ with the same period homomorphism coincide.
--
--   This is the injectivity of the period (Eichler–Shimura) map sending a weight-2 cusp form on $\Gamma_0(N)$ to its character of periods on $\Gamma_0(N)$. It is used to transfer linear independence of cusp forms from period homomorphisms, in [`CuspForm.linearIndependent_complex_of_linearIndependent_int`](thm.html#CuspForm.linearIndependent_complex_of_linearIndependent_int), and in the construction of parabolic realizations, [`ModularCurve.Period.exists_parabolicRealization`](thm.html#ModularCurve.Period.exists_parabolicRealization).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_periodMap_injective.lean

import Definitions.Def_ModularCurve_PeriodMapBundled

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

theorem ModularCurve.periodMap_injective {N : ℕ} [NeZero N] :
    Function.Injective (ModularCurve.periodMap N) := by sorry
