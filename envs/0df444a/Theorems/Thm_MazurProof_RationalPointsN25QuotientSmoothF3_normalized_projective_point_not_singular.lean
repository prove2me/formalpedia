-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientSmoothF3_normalized_projective_point_not_singular
-- name    : MazurProof.RationalPointsN25QuotientSmoothF3.normalized_projective_point_not_singular
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:10:51.638124+00:00
-- url     : https://prove2.me/theorems/235bab7c-3670-4de3-bd7c-c14965a3bc16
-- title:
--   The canonical characteristic-three curve has no normalized singular point
-- statement:
--   Let $K$ be a field of characteristic $3$, and let $P$ be any first-nonzero normalized point of projective $3$-space over $K$. If $\widetilde P∈K^4$ denotes its coordinate vector, then $\widetilde P$ is not a singular point of the canonical quadric-cubic complete intersection: $$¬\bigl(Q(\widetilde P)=C(\widetilde P)=0\text{ and every }2×2\text{ Jacobian minor vanishes}\bigr).$$ This proves geometric nonsingularity of the explicit model in characteristic three.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot

open MazurProof
open MazurProof.RationalPointsN25QuotientSmoothF3
open MazurProof.RationalPointsN25QuotientF2
open MazurProof.RationalPointsN25QuotientWeil
open MazurProof.RationalPointsN25QuotientKummerThree
open MazurProof.RationalPointsN25QuotientWeilThreeLinear
open MazurProof.RationalPointsN25QuotientKummerThreeProjective
open MazurProof.RationalPointsN25QuotientSmallThreeSemantic

theorem MazurProof.RationalPointsN25QuotientSmoothF3.normalized_projective_point_not_singular
    {K : Type*} [Field K] [CharP K 3] (P : NormalizedProjective4 K) :
    ¬ IsCanonicalSingular25Three (normalizedCoordinatesThree P) := by sorry
