-- Prove2me | Theorems.Thm_GOSNIZK_BGNCommit_unique_trapdoor_opening
-- name    : GOSNIZK.BGNCommit.unique_trapdoor_opening
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:11.463445+00:00
-- url     : https://prove2.me/theorems/b24d2c51-1bd6-48b1-acda-c5a45cf465b7
-- title:
--   Proof of Theorem 2 — when $h$ has order $n$, the opening to any message is unique
-- statement:
--   Let $(p, q, \mathbb G, \mathbb G_T, e, g)$ be a BGN bilinear group with $n = pq$ and let $h = g^x$ with $x \in \mathbb Z_n^*$ be a perfectly hiding key. For every commitment $c \in \mathbb G$ and every message $m' \in \mathbb Z_n$ there is exactly one randomizer $r' \in \mathbb Z_n$ with
--   $$g^{m'} h^{r'} = c .$$
--
--   Uniqueness of the opening is what makes the trapdoor opening of a uniformly random commitment uniformly distributed (perfect trapdoor opening indistinguishability).
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 9, proof of Theorem 2

import Mathlib
import Definitions.Def_GOSNIZK_BGNCommit_BGNSetup
import Definitions.Def_GOSNIZK_BGNCommit_Scheme

namespace GOSNIZK.BGNCommit

theorem unique_trapdoor_opening {G GT : Type*} [CommGroup G] [Fintype G] [CommGroup GT]
    [Fintype GT] (S : BGNSetup G GT) (h : G) (x : ZMod S.n) (hkey : S.IsHidingKey h x)
    (c : G) (m' : ZMod S.n) :
    ∃! r' : ZMod S.n, S.com h m' r' = c := by sorry

end GOSNIZK.BGNCommit
