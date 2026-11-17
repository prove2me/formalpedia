-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientSmoothF2_normalized_projective_point_not_singular
-- name    : MazurProof.RationalPointsN25QuotientSmoothF2.normalized_projective_point_not_singular
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:07:21.132216+00:00
-- url     : https://prove2.me/theorems/512fca38-f10f-4867-a31a-15454ee11fca
-- title:
--   No normalized canonical projective point is singular in characteristic two
-- statement:
--   Let $K$ be a field of characteristic $2$, and let $P$ be a normalized projective point in four coordinates. Then its normalized coordinate vector is not a singular point of the characteristic-two canonical complete intersection: $$\neg\operatorname{Sing}_{2}(P).$$ This combines the four chart certificates into global smoothness on projective points.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot

open MazurProof
open MazurProof.RationalPointsN25QuotientSmoothF2
open MazurProof.RationalPointsN25QuotientF2
open MazurProof.RationalPointsN25QuotientWeil

theorem MazurProof.RationalPointsN25QuotientSmoothF2.normalized_projective_point_not_singular
    {K : Type*} [Field K] [CharP K 2] (P : NormalizedProjective4 K) :
    ¬ IsCanonicalSingular25CharTwo (normalizedCoordinates25 P) := by sorry
