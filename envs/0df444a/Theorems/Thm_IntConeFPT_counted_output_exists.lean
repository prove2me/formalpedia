-- Prove2me | Theorems.Thm_IntConeFPT_counted_output_exists
-- name    : IntConeFPT.counted_output_exists
-- status  : Proved
-- author  : @ohnesorgefelix
-- created : 2026-11-25T11:41:38.994012+00:00
-- url     : https://prove2.me/theorems/d2ce76cb-b9ed-4165-9961-fad3d966acc8
-- title:
--   Attainment and rational sparse certificates for counted optimization
-- statement:
--   For every valid instance and count limit, a correct counted output exists. In the feasible case this includes a certificate of rational generators with positive integral multiplicities and at most $2^{2d+1}$ generators per type. The certificate competes with every real feasible representation obeying the same count limit. This is the semantic part of Proposition 14; it says nothing about the running time needed to find an output.
-- source:
--   Jansen–Ohnesorge–Schumacher, https://arxiv.org/abs/2609.31328, Proposition 14, pp.16–17 (the output and certificate specification, without the time bound).

import Definitions.Def_IntConeFPT_Problem
open IntConeFPT

theorem IntConeFPT.counted_output_exists (I : Instance) (hI : I.Valid) (N : ℕ) :
    ∃ o : Output I, o.CorrectN N := by sorry
