-- Prove2me | Theorems.Thm_ModularCurve_isRational_place_modularFunctionFieldBar
-- name    : ModularCurve.isRational_place_modularFunctionFieldBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/40d56426-e797-5c7e-8b5c-90afbfa84894
-- title:
--   Places of ℚ̄(X₀(N)) over ℚ̄ are rational
-- statement:
--   Fix a natural number $N \neq 0$ and let $F =$ `modularFunctionFieldBar N` be the intermediate field of the Laurent series field $\overline{\mathbb Q}((q))$ over $\overline{\mathbb Q}$ (with $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ`) obtained as `laurentBaseChange`, that is, the subfield generated over $\overline{\mathbb Q}$ by the image under the coefficient embedding `coeffEmb` of `modularFunctionFieldFull N`, the latter being the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the family `divisorExpansions N`. Let $P$ be a place of $F$ over $\overline{\mathbb Q}$ in the sense of the structure [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22): a valuation subring $\mathcal{O}_P \subseteq F$ containing the image of $\overline{\mathbb Q}$, distinct from $F$ itself, and whose underlying ring is a principal ideal ring. The conclusion is that $P$ is rational, i.e. `P.IsRational` holds: the structure map from $\overline{\mathbb Q}$ to the residue field of the local ring $\mathcal{O}_P$ is surjective, so that $\overline{\mathbb Q} \to \kappa(P)$ is an isomorphism.
--
--   This is the standard fact that over an algebraically closed constant field every place of a one-variable function field has degree one, applied to the modular function field of level $N$; equivalently, the closed points of $X_0(N)$ over $\overline{\mathbb Q}$ are $\overline{\mathbb Q}$-rational. It is what makes evaluation of functions at a place return an honest element of $\overline{\mathbb Q}$, and is used throughout the subsequent work on Deligne–Rapoport models and on integrality at nodes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isRational_place_modularFunctionFieldBar.lean

import Mathlib
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve
open AlgebraicCurve

theorem ModularCurve.isRational_place_modularFunctionFieldBar (N : ℕ) [NeZero N]
    (P : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) : P.IsRational := by sorry
