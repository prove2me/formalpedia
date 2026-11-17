-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientSmoothF3_yChart_xw_minor_second_branch25Three
-- name    : MazurProof.RationalPointsN25QuotientSmoothF3.yChart_xw_minor_second_branch25Three
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:09:40.747108+00:00
-- url     : https://prove2.me/theorems/d204461b-f278-42fa-986b-e8258b9ec78b
-- title:
--   The $xw$ Jacobian minor on the second $y$-chart branch is $z^2-z$
-- statement:
--   Let $K$ be a field of characteristic $3$ and consider the branch point $(0,1,z,1+z)$. Then the $xw$ Jacobian minor is $$M_{xw}(0,1,z,1+z)=z^2-z.$$ This gives the nonvanishing test on the second branch of the $y$-chart.
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

theorem MazurProof.RationalPointsN25QuotientSmoothF3.yChart_xw_minor_second_branch25Three
    {K : Type*} [Field K] [CharP K 3] (z : K) :
    (canonicalJacobianMinors25Three
      (⟨0, 1, z, 1 + z⟩ : Coordinates4 K)).xw = z ^ 2 - z := by sorry
