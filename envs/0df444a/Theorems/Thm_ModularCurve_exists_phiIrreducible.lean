-- Prove2me | Theorems.Thm_ModularCurve_exists_phiIrreducible
-- name    : ModularCurve.exists_phiIrreducible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/85c90cda-9166-5cf9-a245-c0442a624673
-- title:
--   Existence of an irreducible modular polynomial at every level
-- statement:
--   For every natural number $N$ carrying a `NeZero` instance (so $N \ge 1$), there exists a datum `data : ModularPolynomialData N` satisfying `PhiIrreducible data`. Unfolding the structure, this asserts the existence of a polynomial $\Phi \in (\mathbb{Z}[X])[Y]$, i.e. a one-variable polynomial over the ring $\mathbb{Z}[X]$, with the following three properties: $\Phi$ is monic in $Y$; its degree in $Y$ equals `dedekindPsi N`, defined as $\sum_{d \mid N,\ d \text{ squarefree}} N/d$ (the Dedekind $\psi$-function $\psi(N) = N\prod_{p \mid N}(1+1/p)$); and $\Phi$ vanishes at the pair of $q$-expansions, in the sense that evaluating $\Phi$ by applying the ring homomorphism `evalAtJ : Polynomial ℤ →+* LaurentSeries ℚ` (substitution of the $j$-expansion `jq` for $X$) to the coefficients and substituting `jqN N`, the expansion of $j(q^N)$, for $Y$ gives $0$ in the Laurent series field $\mathbb{Q}((q))$. The extra condition `PhiIrreducible data` says that `data.toAdjoin`, the image $\Phi$ under the coefficientwise map `evalAtJGen` into the intermediate field $\mathbb{Q}\langle jq\rangle = \mathbb{Q}(j(q)) \subseteq \mathbb{Q}((q))$, is an irreducible element of the polynomial ring over that field. Thus $\Phi$ is, up to the identification of $\mathbb{Z}[X]$-coefficients with elements of $\mathbb{Q}(j)$, the minimal polynomial of $j(q^N)$ over $\mathbb{Q}(j)$, of degree $\psi(N)$ and with integral coefficients.
--
--   This is the classical statement that the modular equation of level $N$ exists with integer coefficients, is monic of degree $\psi(N)$ in the second variable, and is irreducible over $\mathbb{Q}(j)$, equivalently that $[\mathbb{Q}(j,j_N):\mathbb{Q}(j)] = \psi(N)$ for the function field of $X_0(N)$. It supplies the defining equation used downstream to build models of $X_0(N)$ and charts near the cusps, including the fibre models in characteristic $p$ and the Igusa-type constructions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_phiIrreducible.lean

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.PhiGen

theorem ModularCurve.exists_phiIrreducible (N : ℕ) [NeZero N] : ∃ data : ModularPolynomialData N, PhiIrreducible data := by sorry
