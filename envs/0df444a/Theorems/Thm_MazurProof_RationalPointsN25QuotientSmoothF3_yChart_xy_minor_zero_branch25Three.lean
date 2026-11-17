-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientSmoothF3_yChart_xy_minor_zero_branch25Three
-- name    : MazurProof.RationalPointsN25QuotientSmoothF3.yChart_xy_minor_zero_branch25Three
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:08:41.701897+00:00
-- url     : https://prove2.me/theorems/1b0c5457-c8bb-4912-bdb3-5afa2627505e
-- title:
--   The $xy$ Jacobian minor equals one on the first exceptional $y$-chart point
-- statement:
--   Let $K$ be a field of characteristic $3$. At the point $(0,1,-1,0)$, the $xy$ minor of the canonical Jacobian satisfies $$M_{xy}(0,1,-1,0)=1.$$ This immediately excludes singularity on the zero-$w$ branch.
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

theorem MazurProof.RationalPointsN25QuotientSmoothF3.yChart_xy_minor_zero_branch25Three
    {K : Type*} [Field K] [CharP K 3] :
    (canonicalJacobianMinors25Three
      (⟨0, 1, -1, 0⟩ : Coordinates4 K)).xy = 1 := by sorry
