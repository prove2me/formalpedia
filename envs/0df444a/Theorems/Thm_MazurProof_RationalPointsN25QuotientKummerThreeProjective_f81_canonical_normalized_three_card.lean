-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThreeProjective_f81_canonical_normalized_three_card
-- name    : MazurProof.RationalPointsN25QuotientKummerThreeProjective.f81_canonical_normalized_three_card
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:17:52.347422+00:00
-- url     : https://prove2.me/theorems/c890421c-d794-43d6-94e2-96b0defbd0f3
-- title:
--   The canonical model has eighty-nine normalized points over $\mathbf F_{81}$
-- statement:
--   Let $C/\mathbf F_{81}$ be the canonical level-$25$ model cut out by the canonical quadric and cubic, and let $C^{\mathrm{norm}}(\mathbf F_{81})$ be its first-nonzero normalized projective representatives, tested with the field-semantic equations. Then
--
--   $$|C^{\mathrm{norm}}(\mathbf F_{81})|=89.$$
--
--   This transports the Segre count back to the original canonical coordinates.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot
import Definitions.Def_N25_ExplicitKummerThreeF81
import Definitions.Def_N25_ExplicitKummerThreeProjective

open MazurProof
open MazurProof.RationalPointsN25QuotientKummerThreeProjective
open MazurProof.RationalPointsN25QuotientF2
open MazurProof.RationalPointsN25QuotientWeil
open MazurProof.RationalPointsN25QuotientWeilThree
open MazurProof.RationalPointsN25QuotientKummerThree
open MazurProof.RationalPointsN25QuotientKummerThreeF81
open scoped BigOperators

theorem MazurProof.RationalPointsN25QuotientKummerThreeProjective.f81_canonical_normalized_three_card :
    Nat.card {P : NormalizedProjective4 F81 // IsCanonicalNormalizedThree P} =
      89 := by sorry
