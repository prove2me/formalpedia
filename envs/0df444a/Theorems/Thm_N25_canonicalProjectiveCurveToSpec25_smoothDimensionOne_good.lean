-- Prove2me | Theorems.Thm_N25_canonicalProjectiveCurveToSpec25_smoothDimensionOne_good
-- name    : N25.canonicalProjectiveCurveToSpec25_smoothDimensionOne_good
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:01:20.029416+00:00
-- url     : https://prove2.me/theorems/33c9e24c-9f72-4740-9ba5-461aadc841c5
-- title:
--   The canonical projective model is smooth of relative dimension one at $2$ and $3$
-- statement:
--   Let $p$ be a prime equal to $2$ or $3$, let $K$ be a field of characteristic $p$, let $C_K$ be the canonical projective curve, and let $π:C_K→\operatorname{Spec}(K)$ be its structure morphism. Then $$π\text{ is smooth of relative dimension }1.$$ This is the full good-reduction statement obtained by gluing the four smooth affine charts.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CanonicalProjectiveCharts
import Definitions.Def_N25_CanonicalChartDehomogenization
import Definitions.Def_N25_CanonicalChartPresentations
import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot

set_option backward.isDefEq.respectTransparency.types false
universe u
open N25
open AlgebraicGeometry CategoryTheory

theorem N25.canonicalProjectiveCurveToSpec25_smoothDimensionOne_good
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3)
    (K : Type u) [Field K] [CharP K p] :
    SmoothOfRelativeDimension 1 (canonicalProjectiveCurveToSpec25 K) := by sorry
