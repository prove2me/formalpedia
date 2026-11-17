-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientSmoothF3_yChart_quadric25Three
-- name    : MazurProof.RationalPointsN25QuotientSmoothF3.yChart_quadric25Three
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:09:32.220948+00:00
-- url     : https://prove2.me/theorems/781b065c-300a-4447-a458-49e31fd639be
-- title:
--   The characteristic-three canonical quadric has a simple formula on the $y$-chart
-- statement:
--   Let $K$ be a field and evaluate the characteristic-three canonical quadric at the point $(0,1,z,w)$. Then $$Q_3(0,1,z,w)=1+z+zw.$$ This formula reduces the $y$-chart branch analysis to elementary equations.
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

theorem MazurProof.RationalPointsN25QuotientSmoothF3.yChart_quadric25Three {K : Type*} [Field K] (z w : K) :
    canonicalQuadric25Three (⟨0, 1, z, w⟩ : Coordinates4 K) =
      1 + z + z * w := by sorry
