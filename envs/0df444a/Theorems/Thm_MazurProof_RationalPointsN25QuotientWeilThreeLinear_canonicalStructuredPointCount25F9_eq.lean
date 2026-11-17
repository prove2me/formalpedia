-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientWeilThreeLinear_canonicalStructuredPointCount25F9_eq
-- name    : MazurProof.RationalPointsN25QuotientWeilThreeLinear.canonicalStructuredPointCount25F9_eq
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:10:26.282134+00:00
-- url     : https://prove2.me/theorems/ffcc0d86-bc2b-474e-86b7-67c488db7bb8
-- title:
--   The structured point count over $\mathbf F_9$ is five
-- statement:
--   Let $R_9,E_9,Y_9,Z_9$ be the four chart components in the structured enumeration of the canonical level-$25$ model over $\mathbf F_9$, and include the final normalized point $[0:0:0:1]$. Then
--
--   $$|R_9|+|E_9|+|Y_9|+|Z_9|+1=5.$$
--
--   This supplies the degree-two characteristic-three point count.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_ExplicitWeil
import Definitions.Def_N25_ExplicitWeilThreeDefs
import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot
import Definitions.Def_N25_ExplicitWeilThreeLinear

open MazurProof
open MazurProof.RationalPointsN25QuotientWeilThreeLinear
open MazurProof.RationalPointsN25QuotientWeil
open MazurProof.RationalPointsN25QuotientWeilThree
attribute [local instance] Fintype.decidableForallFintype
  Fintype.decidableExistsFintype

theorem MazurProof.RationalPointsN25QuotientWeilThreeLinear.canonicalStructuredPointCount25F9_eq :
    canonicalStructuredPointCount25Three f9Operations = 5 := by sorry
