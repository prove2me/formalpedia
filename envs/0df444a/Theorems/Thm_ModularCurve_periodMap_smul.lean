-- Prove2me | Theorems.Thm_ModularCurve_periodMap_smul
-- name    : ModularCurve.periodMap_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/5f0ced97-4bf3-576c-b949-983f2831867f
-- title:
--   Homogeneity of the weight-two period map
-- statement:
--   Fix a natural number $N$, a complex scalar $c$ and a cusp form $f$ of weight $2$ for $\Gamma_0(N)$. The assertion is that the period map in level $N$ is homogeneous: $\mathrm{periodMap}\,N\,(c\cdot f) = c\cdot(\mathrm{periodMap}\,N\,f)$, an identity of additive homomorphisms $\mathrm{Additive}\,\Gamma_0(N) \to \mathbb{C}$, the scalar acting pointwise on the target. Here [`ModularCurve.periodMap N f`](def/ModularCurve_PeriodMapBundled.html#L20) is defined by cases: if some $F : \mathbb{H} \to \mathbb{C}$ satisfies `HasEquivariantPrimitive N f F`, that is (i) $F \circ \mathrm{ofComplex}$ has derivative $f(\tau)$ at every $\tau \in \mathbb{H}$, (ii) $F \to 0$ along the filter $\mathrm{atImInfty}$, (iii) $F$ is an equivariant primitive for $\Gamma_0(N)$, so that for each $\gamma$ the function $z \mapsto F(\gamma\cdot z) - F(z)$ is constant, with value the period of $\gamma$, and (iv) for each $\delta \in \mathrm{SL}_2(\mathbb{Z})$ the function $w \mapsto F(\delta\cdot w)$ has a limit along $\mathrm{atImInfty}$, then `periodMap N f` is the homomorphism $\gamma \mapsto$ (period of $\gamma$) attached to a chosen such $F$; otherwise it is the zero homomorphism. No positivity hypothesis on $N$ is imposed: the level $N = 0$ case is included.
--
--   This is the scalar-homogeneity half of the statement that $f \mapsto \mathrm{periodMap}\,N\,f$ is a $\mathbb{C}$-linear map from weight-two cusp forms on $\Gamma_0(N)$ to additive characters of $\Gamma_0(N)$. Together with additivity it yields the bundled linear period map [`ModularCurve.existsPeriodMapLinear`](thm.html#ModularCurve.existsPeriodMapLinear), and it is used in the statements describing the action of Hecke operators on the period map of a normalised eigenform.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_periodMap_smul.lean

import Definitions.Def_ModularCurve_PeriodMapBundled

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

theorem ModularCurve.periodMap_smul {N : ℕ} (c : ℂ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    ModularCurve.periodMap N (c • f) = c • ModularCurve.periodMap N f := by sorry
