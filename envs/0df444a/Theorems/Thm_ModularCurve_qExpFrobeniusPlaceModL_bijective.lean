-- Prove2me | Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_bijective
-- name    : ModularCurve.qExpFrobeniusPlaceModL_bijective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/b78cec26-de94-558a-8a54-0862528577fd
-- title:
--   The q-expansion Frobenius acts bijectively on places
-- statement:
--   Let $K$ be an algebraically closed field of characteristic a prime $p$, and let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb{Z})$. Write $F =$ [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101) for the intermediate field of the Laurent series field $K((q))$ obtained by adjoining to $K$ the set [`ModularCurve.intFormRatiosC K Γ`](def/ModularCurve_X1.html#L83) of reductions of ratios of integral $q$-expansions attached to $\Gamma$. A place of $F$ over $K$, in the sense of [`AlgebraicCurve.Place K F`](def/AlgebraicCurve_DivisorClassGroup.html#L22), is a valuation subring of $F$ that contains the image of $K$ under the structure map, is not all of $F$, and is a principal ideal ring. The $K$-algebra endomorphism [`ModularCurve.qExpFrobeniusModL K Γ p`](def/ModularCurve_QExpFrobeniusModL.html#L76) of $F$ is the substitution $q \mapsto q^{p}$ on Laurent series (the map `qExpand`, which rescales the exponents by $p$), and [`ModularCurve.qExpFrobeniusPlaceModL K Γ p`](def/ModularCurve_QExpFrobeniusModL.html#L132) sends a place $w$ of $F$ over $K$ to its restriction along this endomorphism, that is to the place whose valuation subring is the preimage of that of $w$. The assertion is that this self-map of the set of places of $F$ over $K$ is bijective.
--
--   The map in question is the action on places of the relative Frobenius of the modular curve attached to $\Gamma$ in characteristic $p$, presented on the $q$-expansion model of its function field; bijectivity is the statement that Frobenius is a purely inseparable isomorphism on the underlying set of closed points. It is one of the ingredients in the characteristic-$p$ analysis of the modular curve and its supersingular points, and is used widely in the later parts of that analysis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_qExpFrobeniusPlaceModL_bijective.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.qExpFrobeniusPlaceModL_bijective
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
    Function.Bijective (ModularCurve.qExpFrobeniusPlaceModL K Γ p) := by sorry
