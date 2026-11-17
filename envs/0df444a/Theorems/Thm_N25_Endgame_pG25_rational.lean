-- Prove2me | Theorems.Thm_N25_Endgame_pG25_rational
-- name    : N25.Endgame.pG25_rational
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:55:24.1735+00:00
-- url     : https://prove2.me/theorems/3633a161-2f70-4dcf-ab4c-5c6d3d685ebe
-- title:
--   Each selected geometric cusp is rational over $ℚ$
-- statement:
--   Let $p_i^G$ be the $i$th selected geometric cusp. It has degree one and is fixed by every arithmetic Galois automorphism:
--
--   $$deg(p_i^G)=1\quad\land\quad σp_i^G=p_i^G\ \text{for all }σ∈Gal(\overline{ℚ}/ℚ).$$
--
--   This places the selected cusp differences in the rational fixed subgroup of the Jacobian.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_SelectedCusps

set_option autoImplicit false
open N25
open N25.Endgame

theorem N25.Endgame.pG25_rational (i : Fin 5) : IsRationalGeomPlace (pG25 i) := by sorry
