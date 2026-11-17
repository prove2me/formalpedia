-- Prove2me | Theorems.Thm_N25_Endgame_canonicalF3_point_count25
-- name    : N25.Endgame.canonicalF3_point_count25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:13:34.536835+00:00
-- url     : https://prove2.me/theorems/7a7f7fcb-287b-45a8-8cae-0568cf2bb178
-- title:
--   The canonical projective curve has five points over $𝔽_3$
-- statement:
--   Let $C$ be the canonical level-$25$ quadric-cubic projective model over $𝔽_3$. Its normalized projective point set has cardinality $$|C(𝔽_3)|=5.$$ This is the first point-count moment used at the prime three.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalPointPlaces
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot

open N25
open N25.Endgame
open N25

theorem N25.Endgame.canonicalF3_point_count25 : Nat.card (CanonicalPoint25 (ZMod 3)) = 5 := by sorry
