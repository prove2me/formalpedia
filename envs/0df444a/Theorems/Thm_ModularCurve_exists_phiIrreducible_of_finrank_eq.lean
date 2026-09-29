-- Prove2me | Theorems.Thm_ModularCurve_exists_phiIrreducible_of_finrank_eq
-- name    : ModularCurve.exists_phiIrreducible_of_finrank_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/e71af2d3-396a-597b-a0df-2a757b4696b3
-- title:
--   Irreducible modular polynomial datum from degree ψ(N)
-- statement:
--   Let $N$ be a natural number, nonzero as a typeclass hypothesis. Inside the field of Laurent series $\mathrm{LaurentSeries}\,\mathbb{Q}$ (Hahn series over $\mathbb{Q}$ with integer exponents) consider the element `jq` $= q^{-1}\cdot j_{\mathrm{num}}$, the product of the Hahn monomial $q^{-1}$ with the image over $\mathbb{Q}$ of the integral power series `jNum`, and its $N$-th substitution `jqN N`, the image of `jq` under the ring homomorphism `qExpand` induced by $q \mapsto q^{N}$ (embedding of exponents along multiplication by $N$ on $\mathbb{Z}$). The hypothesis is that the intermediate field $\mathbb{Q}(jq)(jqN\,N)$, generated over the subfield $\mathbb{Q}(jq)$ by `jqN N`, has finite rank exactly `dedekindPsi N` $=\sum_{d\mid N,\ d\ \text{squarefree}} N/d$ as a module over $\mathbb{Q}(jq)$. The conclusion asserts the existence of a `ModularPolynomialData N`, that is a polynomial $\Phi \in \mathbb{Z}[X][Y]$ which is monic in $Y$, has $Y$-degree equal to `dedekindPsi N`, and satisfies $\Phi = 0$ after substituting `jqN N` for $Y$ and applying to the coefficients the ring homomorphism `evalAtJ : ℤ[X] → LaurentSeries ℚ` sending $X$ to `jq`, together with the property `PhiIrreducible`: the polynomial obtained from $\Phi$ by mapping its coefficients along `evalAtJGen` into $\mathbb{Q}(jq)$ is irreducible in $\mathbb{Q}(jq)[Y]$.
--
--   This is the existence of the classical modular equation of level $N$: an irreducible modular polynomial $\Phi_N$ with integral coefficients, monic and of degree $\psi(N)$ in the second variable, vanishing at $(j(q), j(q^N))$ — obtained here from the degree equality $[\mathbb{Q}(j)(j(q^N)):\mathbb{Q}(j)] = \psi(N)$, which is established separately level by level. It feeds the unconditional existence statement [`ModularCurve.exists_phiIrreducible`](thm.html#ModularCurve.exists_phiIrreducible), the computation [`ModularCurve.finrank_adjoin_jqN_eq_dedekindPsi`](thm.html#ModularCurve.finrank_adjoin_jqN_eq_dedekindPsi), and the generation of the function field of $X_0(N)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_phiIrreducible_of_finrank_eq.lean

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.PhiGen

theorem ModularCurve.exists_phiIrreducible_of_finrank_eq (N : ℕ) [NeZero N] (h : Module.finrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) ({jqN N} : Set (LaurentSeries ℚ))) = dedekindPsi N) : ∃ data : ModularPolynomialData N, PhiIrreducible data := by sorry
