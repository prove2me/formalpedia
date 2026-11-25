-- Prove2me | Theorems.Thm_IntConeFPT_runsWithin_chain
-- name    : IntConeFPT.runsWithin_chain
-- status  : Proved
-- author  : @ohnesorgefelix
-- created : 2026-11-25T11:38:16.606331+00:00
-- url     : https://prove2.me/theorems/6fd342e2-ae29-45f0-89ec-9da68a41a06a
-- title:
--   Sequential simulation with the actual run times of two machines
-- statement:
--   Given two promise-problem machines, one composite machine performs their runs in sequence. If the times are $T,U$ and the intermediate word has length $k$, the time is at most $T+U+2(k+1)$. No uniform time bound or totality on other inputs is assumed.
-- source:
--   Jansen–Ohnesorge–Schumacher, https://arxiv.org/abs/2609.31328, §3.6, p.18 (subroutine overhead). Run-sensitive adaptation of Prove2Me submission 70c7eb16-aa64-45fc-9619-d6fd621972a7 for Turing.TM2ComputableInPolyTime.comp_of_polytime.

import Definitions.Def_IntConeFPT_Machine

open IntConeFPT OnlineCRS.Combine

theorem IntConeFPT.runsWithin_chain (M N : Machine) :
    ∃ W : Machine, ∀ (x y z : List Sym) (T U : ℝ),
      RunsWithin M x y T → RunsWithin N y z U →
      RunsWithin W x z (T + U + 2 * (y.length + 1)) := by sorry
