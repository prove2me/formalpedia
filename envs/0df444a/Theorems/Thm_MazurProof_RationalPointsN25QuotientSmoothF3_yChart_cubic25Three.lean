-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientSmoothF3_yChart_cubic25Three
-- name    : MazurProof.RationalPointsN25QuotientSmoothF3.yChart_cubic25Three
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:08:30.307382+00:00
-- url     : https://prove2.me/theorems/3824e07e-2b55-43fb-96b4-2cd402a118d8
-- title:
--   The characteristic-three canonical cubic factors on the $y$-chart
-- statement:
--   Let $K$ be a field and evaluate the characteristic-three canonical cubic at $(0,1,z,w)$. Then $$C_3(0,1,z,w)=zw(1+z-w).$$ This factorization separates the branches used in the $y$-chart smoothness proof.
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

theorem MazurProof.RationalPointsN25QuotientSmoothF3.yChart_cubic25Three {K : Type*} [Field K] (z w : K) :
    canonicalCubic25Three (⟨0, 1, z, w⟩ : Coordinates4 K) =
      z * w * (1 + z - w) := by sorry
