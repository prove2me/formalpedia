-- Prove2me | Theorems.Thm_KServer_manhattan_three_server
-- name    : KServer.manhattan_three_server
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T12:49:40.939288+00:00
-- url     : https://prove2.me/theorems/a9b88cb1-2594-4f0a-83d5-6c7852cd8595
-- title:
--   Three servers in the Manhattan plane are $3$-competitive
-- statement:
--   For every initial configuration $C_0$ of three servers in the Manhattan plane $(\mathbb{R}^2, \ell^1)$ — the plane with distance $d(x,y) = |x_0 - y_0| + |x_1 - y_1|$ — there is a deterministic online $3$-server algorithm starting at $C_0$ that is $3$-competitive: for some additive constant $a$ independent of the request sequence, its total movement cost on every request sequence $\sigma$ is at most $3 \cdot \mathrm{OPT}(C_0, \sigma) + a$, where $\mathrm{OPT}$ is the optimal offline cost from the same initial configuration.
-- source:
--   W. Bein, M. Chrobak, L. Larmore, The 3-Server Problem in the Plane, Theoretical Computer Science 289(1), pp. 335-354, 2002 (the Work Function Algorithm is 3-competitive in the Manhattan plane). Unified reproof: C. Coester, E. Koutsoupias, Towards the k-server conjecture: a unifying potential, pushing the frontier to the circle, ICALP 2021, https://arxiv.org/abs/2102.10474

import Mathlib
import Definitions.Def_KServer_model

namespace KServer

theorem manhattan_three_server (C₀ : Config 3 (PiLp 1 fun _ : Fin 2 => ℝ)) :
    ∃ A : OnlineAlgorithm 3 (PiLp 1 fun _ : Fin 2 => ℝ),
      A.conf [] = C₀ ∧ IsCompetitive A 3 := by sorry

end KServer
