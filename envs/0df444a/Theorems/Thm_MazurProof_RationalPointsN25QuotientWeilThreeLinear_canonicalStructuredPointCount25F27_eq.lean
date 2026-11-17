-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientWeilThreeLinear_canonicalStructuredPointCount25F27_eq
-- name    : MazurProof.RationalPointsN25QuotientWeilThreeLinear.canonicalStructuredPointCount25F27_eq
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:11:01.202755+00:00
-- url     : https://prove2.me/theorems/79fff36b-a0ea-4cd5-9d84-cfb1c98b8646
-- title:
--   The structured point count over $\mathbf F_{27}$ is twenty
-- statement:
--   Let $R_{27},E_{27},Y_{27},Z_{27}$ be the four chart components in the structured enumeration of the canonical level-$25$ model over $\mathbf F_{27}$, and include the final point $[0:0:0:1]$. Then
--
--   $$|R_{27}|+|E_{27}|+|Y_{27}|+|Z_{27}|+1=20.$$
--
--   This supplies the degree-three characteristic-three point count.
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

theorem MazurProof.RationalPointsN25QuotientWeilThreeLinear.canonicalStructuredPointCount25F27_eq :
    canonicalStructuredPointCount25Three f27Operations = 20 := by sorry
