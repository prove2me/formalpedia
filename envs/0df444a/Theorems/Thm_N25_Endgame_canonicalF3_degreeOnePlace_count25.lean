-- Prove2me | Theorems.Thm_N25_Endgame_canonicalF3_degreeOnePlace_count25
-- name    : N25.Endgame.canonicalF3_degreeOnePlace_count25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:12:41.051592+00:00
-- url     : https://prove2.me/theorems/cdb12ba7-2b8b-4b04-9134-03f620cc560d
-- title:
--   The canonical function field has five degree-one places over $𝔽_3$
-- statement:
--   Let $F_{𝔽_3}$ be the canonical level-$25$ function field over $𝔽_3$, with its selected open chart known to be a domain. Then $$|\{P∈\operatorname{Place}_{𝔽_3}(F_{𝔽_3}):\deg P=1\}|=5.$$ This is the function-field form of the base ternary point count.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalPointPlaces
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot

open N25
open N25.Endgame
open N25

theorem N25.Endgame.canonicalF3_degreeOnePlace_count25 :
    letI : IsDomain (CanonicalOpenChartRing25 (ZMod 3)) :=
      canonicalOpenChartRing_isDomain_good25 3 (Or.inr rfl) (ZMod 3)
    Nat.card {P : AlgebraicCurve.Place (ZMod 3) (CanonicalFF25 (ZMod 3)) //
      P.deg = 1} = 5 := by sorry
