-- Prove2me | Theorems.Thm_N25_Endgame_canonical_degreeOnePlace_card_eq_points25
-- name    : N25.Endgame.canonical_degreeOnePlace_card_eq_points25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:12:57.274205+00:00
-- url     : https://prove2.me/theorems/48aaf835-298c-4bdb-9ec7-b599ef69debe
-- title:
--   Degree-one places equal canonical projective points in good characteristic
-- statement:
--   Let $p$ be a prime equal to $2$ or $3$, let $K$ be a perfect field of characteristic $p$, let $F_K$ be the canonical function field, and let $C(K)$ be the set of normalized projective $K$-points satisfying the canonical quadric and cubic. Then $$|\{P∈\operatorname{Place}_K(F_K):\deg P=1\}|=|C(K)|.$$ This transports complete projective point counts, including boundary charts, to degree-one places. Formalization note: a proved domain instance for the selected affine chart is installed locally.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalPointPlaces
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot

open N25
open N25.Endgame
open N25

theorem N25.Endgame.canonical_degreeOnePlace_card_eq_points25
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3)
    (K : Type*) [Field K] [PerfectField K] [CharP K p] :
    letI : IsDomain (CanonicalOpenChartRing25 K) :=
      canonicalOpenChartRing_isDomain_good25 p hp K
    Nat.card {P : AlgebraicCurve.Place K (CanonicalFF25 K) // P.deg = 1} =
      Nat.card (CanonicalPoint25 K) := by sorry
