-- Prove2me | Theorems.Thm_ModularCurve_isRational_place_x1FunctionFieldC_of_isAlgClosed
-- name    : ModularCurve.isRational_place_x1FunctionFieldC_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/378c4f0f-abc6-5222-9624-5b970dbd3e70
-- title:
--   Places of the q-expansion function field of X₁(M) are rational
-- statement:
--   Let $p$ be a prime, let $M$ be a nonzero natural number with $5 \le M$ and $p \nmid M$, and let $\Omega$ be an algebraically closed field of characteristic $p$. Write $F =$ [`ModularCurve.x1FunctionFieldC`](def/ModularCurve_X1.html#L134) $\Omega\,M$ for the intermediate field of the field of formal Laurent series over $\Omega$ obtained by adjoining to $\Omega$ the set `intFormRatiosC` $\Omega\,(\mathrm{Gamma1}\,M)$ of $q$-expansion ratios of integral forms for $\Gamma_1(M)$, i.e. the $q$-expansion function field of $X_1(M)$ over $\Omega$. Let $v$ be a place of $F$ over $\Omega$ in the project's sense: a valuation subring of $F$ which contains the image of $\Omega$ under the structure map, is not the whole of $F$, and is a principal ideal ring. The conclusion is that $v$ is rational, meaning by definition that the composite map from $\Omega$ to the residue field of the local ring $v$ is surjective; so the residue field at $v$ is exhausted by the constants.
--
--   This is the standard fact that over an algebraically closed constant field every place of a one-variable function field has residue field equal to the constant field, specialised to the $q$-expansion function field of $X_1(M)$ in characteristic $p \nmid M$. It is used wherever points of the Igusa/modular curve in characteristic $p$ are handled through their places, for instance in the computations of ramification indices and of orders of vanishing of Hasse-root functions along such places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isRational_place_x1FunctionFieldC_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open ModularCurve

theorem ModularCurve.isRational_place_x1FunctionFieldC_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω]
    (v : AlgebraicCurve.Place Ω ↥(ModularCurve.x1FunctionFieldC Ω M)) : v.IsRational := by sorry
