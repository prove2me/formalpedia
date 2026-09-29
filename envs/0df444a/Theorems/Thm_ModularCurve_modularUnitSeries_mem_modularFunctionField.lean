-- Prove2me | Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionField
-- name    : ModularCurve.modularUnitSeries_mem_modularFunctionField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/cf151edf-c330-5738-a8a0-fb1350ee0fe3
-- title:
--   Ogg's unit Δ(q)/Δ(q^ℓ) lies in ℚ(j,j_ℓ)
-- statement:
--   Let $\ell$ be a prime. Write $\mathrm{qExpand}\,\mathbb{Q}\,\ell$ for the ring endomorphism of the Laurent series field $\mathbb{Q}((q))$ obtained by transporting a series along the order-preserving injection $m \mapsto \ell m$ of the exponent group $\mathbb{Z}$, that is, the substitution $q \mapsto q^{\ell}$. Let $\mathrm{deltaSeries} = q \cdot \mathrm{dedekindEtaUnitQ}$ be the Laurent series given by the monomial $q$ times the power series $\prod_{n\ge 1}(1-q^{n})^{24}$, and let $\mathrm{modularUnitSeries}\,\ell = \mathrm{deltaSeries} \cdot (\mathrm{qExpand}\,\mathbb{Q}\,\ell\,\mathrm{deltaSeries})^{-1}$, the formal quotient $\Delta(q)/\Delta(q^{\ell})$ in $\mathbb{Q}((q))$. Let $\mathrm{modularFunctionField}\,\ell$ be the intermediate field of $\mathbb{Q} \subseteq \mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the two elements `jq` and $\mathrm{qExpand}\,\mathbb{Q}\,\ell\,$`jq`. The theorem asserts that $\mathrm{modularUnitSeries}\,\ell$ belongs to $\mathrm{modularFunctionField}\,\ell$: the Laurent series $\Delta(q)/\Delta(q^{\ell})$ is a rational function, with rational coefficients, of `jq` and of its image under $q \mapsto q^{\ell}$.
--
--   This is the rationality statement for Ogg's modular unit on $X_0(\ell)$, whose divisor is supported on the cusps: the quotient $\Delta(\tau)/\Delta(\ell\tau)$ is a function on $X_0(\ell)$ defined over $\mathbb{Q}$. It is used in the construction of explicit units in the coordinate algebras of charts of modular curves, in particular for the chart algebras occurring in the treatment of $X_1$ and of the $\Gamma_H$-level curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_modularUnitSeries_mem_modularFunctionField.lean

import Definitions.Def_ModularCurve_ModularUnit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.modularUnitSeries_mem_modularFunctionField (ℓ : ℕ) [Fact (Nat.Prime ℓ)] : ModularCurve.modularUnitSeries ℓ ∈ ModularCurve.modularFunctionField ℓ := by sorry
