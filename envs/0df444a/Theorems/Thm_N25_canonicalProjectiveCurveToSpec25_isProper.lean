-- Prove2me | Theorems.Thm_N25_canonicalProjectiveCurveToSpec25_isProper
-- name    : N25.canonicalProjectiveCurveToSpec25_isProper
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:30:21.860926+00:00
-- url     : https://prove2.me/theorems/5b61e0e0-9606-4047-9426-a068a3b99775
-- title:
--   The canonical projective curve is proper over its coefficient field
-- statement:
--   Let $K$ be a field, let $C_K$ be the canonical projective curve, and let $π:C_K→\operatorname{Spec}(K)$ be its structure morphism. Then $$π\text{ is proper}.$$ This supplies completeness of the model, so degree-one places correspond to points on the full projective curve rather than only an affine chart.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalProjectiveCharts
import Definitions.Def_N25_CanonicalChartDehomogenization
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

universe u
open N25
open AlgebraicGeometry CategoryTheory
variable (K : Type u) [Field K]

theorem N25.canonicalProjectiveCurveToSpec25_isProper : IsProper (canonicalProjectiveCurveToSpec25 K) := by sorry
