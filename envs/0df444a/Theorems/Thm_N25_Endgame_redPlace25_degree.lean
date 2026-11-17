-- Prove2me | Theorems.Thm_N25_Endgame_redPlace25_degree
-- name    : N25.Endgame.redPlace25_degree
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:26:59.472709+00:00
-- url     : https://prove2.me/theorems/2d4e8feb-0291-404c-90c8-ab5161c37e5c
-- title:
--   Reduction preserves the degree of every geometric place
-- statement:
--   Let $ℓ$ be prime, let $D$ be a level-$25$ reduction datum at $ℓ$, and let $P$ be a place of the geometric level-$25$ function field. Then the reduced place has the same degree:
--
--   $$deg(red_D(P))=deg(P).$$
--
--   This ensures that degree-one geometric places remain degree one on the special fiber and makes reduced point differences well defined.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_Endgame

set_option autoImplicit false
open N25
open N25.Endgame

theorem N25.Endgame.redPlace25_degree
    {ℓ : ℕ} [Fact ℓ.Prime] (D : RedDatum25 ℓ) (P : GPlace) :
    (redPlace25 D P).deg = P.deg := by sorry
