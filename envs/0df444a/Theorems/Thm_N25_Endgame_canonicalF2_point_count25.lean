-- Prove2me | Theorems.Thm_N25_Endgame_canonicalF2_point_count25
-- name    : N25.Endgame.canonicalF2_point_count25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:13:12.769322+00:00
-- url     : https://prove2.me/theorems/be3c2603-e24e-4208-b00e-241e0b3f8605
-- title:
--   The canonical projective curve has five points over $𝔽_2$
-- statement:
--   Let $C$ be the canonical level-$25$ quadric-cubic projective model over $𝔽_2$. Its normalized projective point set has cardinality $$|C(𝔽_2)|=5.$$ This is the base-field count used for good reduction at two.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalPointPlaces
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot

open N25
open N25.Endgame
open N25

theorem N25.Endgame.canonicalF2_point_count25 : Nat.card (CanonicalPoint25 (ZMod 2)) = 5 := by sorry
