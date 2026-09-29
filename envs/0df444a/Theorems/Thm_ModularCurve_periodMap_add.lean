-- Prove2me | Theorems.Thm_ModularCurve_periodMap_add
-- name    : ModularCurve.periodMap_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/30df23ad-0389-54d0-b023-0919ae208afe
-- title:
--   Additivity of the weight-two period map
-- statement:
--   Let $N$ be a natural number and let $f,g$ be cusp forms of weight $2$ for the congruence subgroup $\Gamma_0(N) \le \mathrm{SL}_2(\mathbb{Z})$. The assertion is that the period map is additive: $\mathrm{periodMap}\,N\,(f+g) = \mathrm{periodMap}\,N\,f + \mathrm{periodMap}\,N\,g$ as additive homomorphisms $\mathrm{Additive}\,\Gamma_0(N) \to \mathbb{C}$, the right-hand sum being taken pointwise. Here $\mathrm{periodMap}\,N\,f$ is defined by cases: if some $F : \mathbb{H} \to \mathbb{C}$ satisfies `HasEquivariantPrimitive N f F`, that is, (i) $F \circ \mathrm{ofComplex}$ has complex derivative $f(\tau)$ at every $\tau \in \mathbb{H}$, (ii) $F \to 0$ along the filter $\mathrm{atImInfty}$, (iii) `IsEquivariantPrimitive (Gamma0 N) F` holds, so that for each $\gamma \in \Gamma_0(N)$ the difference $F(\gamma \cdot z) - F(z)$ is a constant, the period of $\gamma$, and (iv) for every $\delta \in \mathrm{SL}_2(\mathbb{Z})$ the function $w \mapsto F(\delta \cdot w)$ has a limit along $\mathrm{atImInfty}$, then $\mathrm{periodMap}\,N\,f$ is the homomorphism $\gamma \mapsto$ (period of $\gamma$) for such a chosen $F$; otherwise it is the zero homomorphism. No positivity hypothesis on $N$ is imposed, so the degenerate level $N = 0$ is included.
--
--   This is the additivity half of the statement that the classical period map of weight-two cusp forms, $f \mapsto (\gamma \mapsto \int^{\gamma z_0}_{z_0} f)$, is $\mathbb{C}$-linear in $f$. It feeds the bundling of the period map into a $\mathbb{C}$-linear map [`ModularCurve.existsPeriodMapLinear`](thm.html#ModularCurve.existsPeriodMapLinear), and is used in the injectivity statement [`ModularCurve.periodMap_injective`](thm.html#ModularCurve.periodMap_injective) and in [`ModularCurve.Period.exists_parabolicRealization`](thm.html#ModularCurve.Period.exists_parabolicRealization).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_periodMap_add.lean

import Definitions.Def_ModularCurve_PeriodMapBundled

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

theorem ModularCurve.periodMap_add {N : ℕ} (f g : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    ModularCurve.periodMap N (f + g) = ModularCurve.periodMap N f + ModularCurve.periodMap N g := by sorry
