-- Prove2me | Theorems.Thm_ModularCurve_existsPeriodMapLinear
-- name    : ModularCurve.existsPeriodMapLinear
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/1906c0ae-a1de-52fd-892b-6f702452d959
-- title:
--   Linearity of the period map at every level
-- statement:
--   For every natural number $N$ the predicate [`ModularCurve.ExistsPeriodMapLinear N`](def/ModularCurve_PeriodHomPair.html#L132) holds, i.e. there is a $\mathbb{C}$-linear map $\mathrm{pml}$ from the space `CuspForm (Gamma0 N) 2` of weight-$2$ cusp forms for $\Gamma_0(N)$ to the additive group of additive-monoid homomorphisms $\mathrm{Additive}(\Gamma_0(N)) \to \mathbb{C}$ (the group $\Gamma_0(N)$ written additively, so that such a homomorphism is exactly a homomorphism of groups $\Gamma_0(N) \to (\mathbb{C},+)$) with the property that $\mathrm{pml}(f) = \mathrm{periodMap}\, N\, f$ for every cusp form $f$. Here `periodMap N f` is defined by a dichotomy: if there exists a function $F : \mathbb{H} \to \mathbb{C}$ satisfying `HasEquivariantPrimitive N f F`, then `periodMap N f` is the period homomorphism attached, via the `IsEquivariantPrimitive` component of that witness's defining property, to a chosen such $F$; otherwise `periodMap N f` is the zero homomorphism. Thus the assertion is that the map $f \mapsto$ `periodMap N f`, which is defined by a choice and hence a priori only a function, is additive and $\mathbb{C}$-homogeneous, for every level $N$, including $N = 0$.
--
--   This is the statement that the classical period map $f \mapsto \mathrm{per}_f$ on weight-$2$ cusp forms for $\Gamma_0(N)$, sending $f$ to the homomorphism recording the periods of an equivariant primitive of $2\pi i f(z)\,dz$, is $\mathbb{C}$-linear. It is the hypothesis through which the period pairing into $H^1(\Gamma_0(N),\mathbb{C})$ is constructed, and it is used in the Eichler–Shimura part of the argument, for instance by [`CohCarrier.exists_eichlerShimura_H1_top`](thm.html#CohCarrier.exists_eichlerShimura_H1_top) and the statements about parabolic homomorphisms and Hecke eigenvalues.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_existsPeriodMapLinear.lean

import Definitions.Def_ModularCurve_PeriodHomPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.existsPeriodMapLinear (N : ℕ) :
    ModularCurve.ExistsPeriodMapLinear N := by sorry
