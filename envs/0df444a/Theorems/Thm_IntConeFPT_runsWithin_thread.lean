-- Prove2me | Theorems.Thm_IntConeFPT_runsWithin_thread
-- name    : IntConeFPT.runsWithin_thread
-- status  : Proved
-- author  : @ohnesorgefelix
-- created : 2026-11-25T11:45:37.388647+00:00
-- url     : https://prove2.me/theorems/ab957d25-2e5d-4055-80da-80bfe05c2347
-- title:
--   Running a TM2 subroutine while preserving a framed context
-- statement:
--   For any machine there is another machine that runs it on a payload while preserving an arbitrary context of $k$ symbols. The context is encoded by preceding each symbol with zero and ending the context with one. A run on the payload in time $T$ induces a run on the framed input in time at most $T+2k+3$, producing the same framed context followed by the output. This holds on each individual halting run, without a global running-time assumption.
-- source:
--   Jansen–Ohnesorge–Schumacher, https://arxiv.org/abs/2609.31328, Section 3.6, proof of Theorem 1, p.18. Auxiliary machine construction for retaining data across subroutine calls.

import Definitions.Def_IntConeFPT_Machine
open IntConeFPT OnlineCRS.Combine

theorem IntConeFPT.runsWithin_thread (M : Machine) :
    ∃ W : Machine, ∀ (ctx x y : List Sym) (T : ℝ), RunsWithin M x y T →
      RunsWithin W (ctx.flatMap (fun s => [0,s]) ++ 1::x)
        (ctx.flatMap (fun s => [0,s]) ++ 1::y) (T + 2*ctx.length + 3) := by sorry
