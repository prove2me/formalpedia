-- Prove2me | Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_eq_qExpArithFrobC_smul
-- name    : ModularCurve.qExpFrobeniusPlaceModL_eq_qExpArithFrobC_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/1d686647-b4a5-58b7-89ab-481b7009ef5a
-- title:
--   Frobenius pullback of places equals arithmetic Frobenius twist
-- statement:
--   Fix a natural number $p$ that is prime, a field $K$ of characteristic $p$ which is perfect, and a subgroup $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$. Let $F =$ [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101) be the intermediate field of $K \subseteq K((q))$ obtained by adjoining to $K$ all quotients $\mathrm{intSeriesC}\,K\,p_f / \mathrm{intSeriesC}\,K\,p_g$ coming from integral $q$-expansions $p_f, p_g$ of modular forms $f, g$ of some weight $k$ for $\Gamma$ with the denominator series nonzero. Let $w$ be a place of $F$ over $K$, that is, a valuation subring of $F$ which contains the image of $K$, is not the whole of $F$, and is a principal ideal ring. The conclusion is an equality of two places of $F$: on one side, [`ModularCurve.qExpFrobeniusPlaceModL K Γ p w`](def/ModularCurve_QExpFrobeniusModL.html#L132), the restriction of $w$ along the $K$-algebra endomorphism [`ModularCurve.qExpFrobeniusModL K Γ p`](def/ModularCurve_QExpFrobeniusModL.html#L76) of $F$ given by the substitution $q \mapsto q^{p}$ on Laurent series; on the other side, the image of $w$ under the action of the semilinear automorphism [`ModularCurve.qExpArithFrobC p K Γ`](def/ModularCurve_QExpCoeffSemilinearAut.html#L188), namely the pair consisting of the coefficientwise automorphism of $F$ induced by the Frobenius $x \mapsto x^{p}$ of $K$ together with that Frobenius itself.
--
--   This is the dictionary between the geometric and the arithmetic Frobenius conventions for places of the $q$-expansion function field in characteristic $p$: pulling a place back along $q \mapsto q^{p}$ is the same as twisting it by the coefficientwise Frobenius. It is used when the supersingular points and nodes in characteristic $p$ of the modular curves of level $\Gamma \cap \Gamma_0(p)$ are matched up, the pairs of places produced by the Frobenius correspondence being identified with pairs produced by the Galois twist.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_qExpFrobeniusPlaceModL_eq_qExpArithFrobC_smul.lean

import Mathlib
import Definitions.Def_ModularCurve_QExpFrobeniusModL
import Definitions.Def_ModularCurve_QExpCoeffSemilinearAut
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open scoped MatrixGroups

theorem ModularCurve.qExpFrobeniusPlaceModL_eq_qExpArithFrobC_smul
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p] [PerfectField K] (Γ : Subgroup SL(2, ℤ))
    (w : AlgebraicCurve.Place K (ModularCurve.qExpFunctionFieldC K Γ)) :
    ModularCurve.qExpFrobeniusPlaceModL K Γ p w = ModularCurve.qExpArithFrobC p K Γ • w := by sorry
