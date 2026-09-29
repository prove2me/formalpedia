-- Prove2me | Theorems.Thm_ModularCurve_periodHomPair_range_eq_parabolicHoms
-- name    : ModularCurve.periodHomPair_range_eq_parabolicHoms
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/d80bdfbd-35c6-5cc4-8b8a-f8b8fdf53b72
-- title:
--   Eichler–Shimura: period pair map onto parabolic homomorphisms
-- statement:
--   Let $N$ be a natural number, assumed nonzero. Consider the $\mathbb{C}$-linear map [`ModularCurve.periodHomPair N`](def/ModularCurve_PeriodHomPair.html#L135) from the product $S_2(\Gamma_0(N)) \times S_2(\Gamma_0(N))$ of two copies of the space of weight-$2$ cusp forms for $\Gamma_0(N)$ to the space of additive homomorphisms from $\Gamma_0(N)$, viewed additively, to $\mathbb{C}$; by definition it is zero unless the predicate `ExistsPeriodMapLinear N` holds, i.e. unless some $\mathbb{C}$-linear map $\mathrm{pml}$ agrees pointwise with the period map `periodMap N`, in which case it sends a pair $(f,g)$ to $(\mathrm{pml}\,f + \mathrm{pml}\,f \circ j) + (\mathrm{pml}\,g - \mathrm{pml}\,g \circ j)$, where $j$ is the conjugation involution `jConjGamma0 N` of $\Gamma_0(N)$ acting by precomposition. The assertion is that the range of this map, as a $\mathbb{C}$-submodule, is exactly [`ModularCurve.Period.parabolicHoms ℂ (Gamma0 N) ℂ`](def/ModularCurve_PeriodMap.html#L62), the submodule of those additive homomorphisms $\varphi$ which vanish on every $\gamma \in \Gamma_0(N)$ whose integral matrix has trace with square equal to $4$.
--
--   This is the surjectivity half of the Eichler–Shimura isomorphism in weight $2$ and level $N$, in the form: the two-variable period map identifies $S_2(\Gamma_0(N))^{\oplus 2}$ with the parabolic part $H^1_{\mathrm{par}}(\Gamma_0(N),\mathbb{C})$ realised here as homomorphisms vanishing on elements of trace $\pm 2$. It is used to transfer statements about parabolic homomorphisms to cusp forms, notably in the Eichler–Shimura comparison [`ModularCurve.periodHomPair_eichlerShimura`](thm.html#ModularCurve.periodHomPair_eichlerShimura) and in the linear independence and Hecke-word vanishing results for cusp forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_periodHomPair_range_eq_parabolicHoms.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodHomPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.periodHomPair_range_eq_parabolicHoms (N : ℕ) [NeZero N] :
    LinearMap.range (ModularCurve.periodHomPair N)
      = ModularCurve.Period.parabolicHoms ℂ (CongruenceSubgroup.Gamma0 N) ℂ := by sorry
