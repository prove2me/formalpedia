-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientSmallThreeSemantic_f9Operations_eq_field
-- name    : MazurProof.RationalPointsN25QuotientSmallThreeSemantic.f9Operations_eq_field
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:18:45.433318+00:00
-- url     : https://prove2.me/theorems/4b93a7bc-217c-4f76-8426-2cd4d55b52f5
-- title:
--   The executable nine-element operations are the field operations
-- statement:
--   Let $F_9$ be the nine-element polynomial-basis carrier endowed with its certified field structure. Its executable ternary operation record equals the operation record coming from that field: $$O_9=O_{\mathrm{field}}(F_9).$$ This licenses transport of the quadratic-extension table count to the semantic curve.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot
import Definitions.Def_N25_ExplicitSmallThreeFields
import Definitions.Def_N25_ExplicitKummerThreeProjective
import Definitions.Def_N25_ExplicitWeilThreeLinear
import Definitions.Def_N25_ExplicitSmallThreeSemantic

open MazurProof
open MazurProof.RationalPointsN25QuotientSmallThreeSemantic
open MazurProof.RationalPointsN25QuotientWeil
open MazurProof.RationalPointsN25QuotientF2
open MazurProof.RationalPointsN25QuotientWeilThree
open MazurProof.RationalPointsN25QuotientWeilThreeLinear
open MazurProof.RationalPointsN25QuotientKummerThree
open MazurProof.RationalPointsN25QuotientKummerThreeProjective
universe u

theorem MazurProof.RationalPointsN25QuotientSmallThreeSemantic.f9Operations_eq_field :
    f9Operations = fieldTernaryOperations F9 := by sorry
