-- Prove2me | Theorems.Thm_IntConeFPT_polynomial_zero_block_writer
-- name    : IntConeFPT.polynomial_zero_block_writer
-- status  : Open
-- author  : @ohnesorgefelix
-- created : 2026-11-24T14:27:38.122696+00:00
-- url     : https://prove2.me/theorems/bbe44f70-eef6-41e8-8eb3-61f062b7eaa9
-- title:
--   Printing a polynomial-length block of zeros on a multi-stack machine
-- statement:
--   Fix a natural exponent $a$. A deterministic multi-stack machine can turn any word of length $L\ge2$ into $L^a$ zero symbols followed by a single one in time $L^e$, for an exponent $e$ depending only on $a$. Only the input length matters. For instance, nested traversals of unary copies of the length enumerate the $a$-tuples of input positions; the empty tuple gives one zero when $a=0$.
-- source:
--   Jansen, Ohnesorge and Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, https://arxiv.org/abs/2609.31328, §2, (2.1), p. 6. Auxiliary machine construction for the polynomial-time requirement; not a separately numbered claim in the source.

import Definitions.Def_IntConeFPT_Machine

open OnlineCRS.Combine IntConeFPT

theorem IntConeFPT.polynomial_zero_block_writer (a : ℕ) :
    ∃ e : ℕ, ∃ W : Machine, ∀ w : List Sym, 2 ≤ w.length →
      RunsWithin W w (List.replicate (w.length ^ a) 0 ++ [1]) ((w.length : ℝ) ^ e) := by sorry
