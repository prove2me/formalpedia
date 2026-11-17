-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientSmallThreeSemantic_f27Operations_eq_field
-- name    : MazurProof.RationalPointsN25QuotientSmallThreeSemantic.f27Operations_eq_field
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:18:37.257207+00:00
-- url     : https://prove2.me/theorems/db974272-b7f6-45ae-b947-ef3cbf41603b
-- title:
--   The executable twenty-seven-element operations are the field operations
-- statement:
--   Let $F_{27}$ be the twenty-seven-element polynomial-basis carrier endowed with its certified field structure. Its executable ternary operation record equals the operation record coming from that field: $$O_{27}=O_{\mathrm{field}}(F_{27}).$$ This licenses transport of the cubic-extension table count to the semantic curve.
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

theorem MazurProof.RationalPointsN25QuotientSmallThreeSemantic.f27Operations_eq_field :
    f27Operations = fieldTernaryOperations F27 := by sorry
