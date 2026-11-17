-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientSmoothF3_zChart_yw_minor_eq_one25Three
-- name    : MazurProof.RationalPointsN25QuotientSmoothF3.zChart_yw_minor_eq_one25Three
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:08:50.246778+00:00
-- url     : https://prove2.me/theorems/6572afa0-ac52-4f10-92c0-ea16e432de86
-- title:
--   The $yw$ Jacobian minor is identically one on the characteristic-three $z$-chart axis
-- statement:
--   Let $K$ be a field and let $w∈K$. At the point $(0,0,1,w)$, the $yw$ minor of the characteristic-three canonical Jacobian satisfies $$M_{yw}(0,0,1,w)=1.$$ This rules out singularities on the remaining $z$-chart branch.
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

theorem MazurProof.RationalPointsN25QuotientSmoothF3.zChart_yw_minor_eq_one25Three
    {K : Type*} [Field K] (w : K) :
    (canonicalJacobianMinors25Three
      (⟨0, 0, 1, w⟩ : Coordinates4 K)).yw = 1 := by sorry
