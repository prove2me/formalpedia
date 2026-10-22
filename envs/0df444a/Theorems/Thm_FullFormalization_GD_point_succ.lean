-- Prove2me | Theorems.Thm_FullFormalization_GD_point_succ
-- name    : FullFormalization.GD.point_succ
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-09T05:46:02.754+00:00
-- url     : https://prove2.me/theorems/2da5dd89-eda3-4fac-ad31-412c4337c03e
-- title:
--   Gradient-descent recursion $p_{k+1} = p_k - \tfrac{1}{L}\nabla f(p_k)$
-- statement:
--   The iterates of gradient descent with step $1/L$ obey
--
--   $$p_{k+1} = p_k - \frac{1}{L}\, \nabla f(p_k), \qquad k \in \mathbb{N},$$
--
--   with exactly one oracle call per step. Here $p_k$ is the $k$-th iterate starting from the origin, $\nabla f(p_k)$ is the gradient reported by the oracle at $p_k$, and $L > 0$ is the smoothness constant, so that $1/L$ is the step size. This is the frozen implementation's loop transcribed step for step: query the oracle at the current point, then move by the step size times the reported gradient.
-- source:
--   《有理动量 Nesterov 紧界与半径归一化五算法共同最坏情形 — 可审计完整证明稿》 (manuscript, 2026-10-08), §21 (strategy 1: GD, step $1/L$), with §19 (the frozen implementation); Lean: FullFormalization.GradientStrategies lines 91-95

-- Generated from F:/20261008/FullFormalization\FullFormalization\GradientStrategies.lean (Phase 3): skeleton subtraction, proof cut at
-- valStart (Stage 2), docstring stripped, declaration hoisted to top
-- level with its fully dotted name; body is `:= by sorry`.
/-
  FullFormalization.GradientStrategies

  Source: `auditable_full_proof_nag_and_five_algorithm_cn.md`, section 21,
  strategies 1 and 2 (source lines 2079-2080):

      1. GD, step `1/L`;
      2. GD, step `1/(2L)`.

  Implementation semantics (source §19 authorises the frozen implementation,
  and §35's cross-check script imports it):
  `F:\Hardy_Run_2026-10-07_001215\workflow\hgcore\blackbox_algos.py`,
  `_gd_fixed_1_over_L` and `_gd_fixed_declared_steps`:

      point = _origin(spec)                      -- the origin
      for _ in range(spec.query_budget):         -- one query per step
          answer = oracle.query(point)
          point = point - size * answer["gradient"]
      oracle.finish(point)                       -- the final point is the output

  with `size = 1/L` for the first strategy and `size = 1/(2L)` for the second.
  Both start from the origin, so — as the implementation's own docstring says —
  the only difference between them is the step size.

  In the normalized coordinates of section 21 the starting point is `z = 0`,
  i.e. `x = x_init`; the two strategies below are written on the raw oracle and
  in normalized coordinates, which is the same thing since `z = 0` is the
  origin of `E`.

  Query bookkeeping: the loop body queries *then* steps, so the `N` queries are
  the iterates `p_0, ..., p_{N-1}` and the reported point is `p_N`.  There is no
  query at the output point (matching §5: no off-by-one, and matching source
  line 312-319 where `g_N` is a proof variable only for the NAG method).
-/

import Mathlib
import Definitions.Def_Coefficients
import Definitions.Def_FunctionClass
import Definitions.Def_GradientStrategies
import Definitions.Def_PortfolioDefinitions
import Theorems.Thm_FullFormalization_descentPoint_succ

open scoped Gradient RealInnerProductSpace

set_option linter.unusedSectionVars false

namespace FullFormalization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The shared fixed-step descent -/









/-! ### Strategy 1: gradient descent with step `1/L` -/

namespace GD

























end GD

/-! ### Strategy 2: gradient descent with step `1/(2L)` -/

namespace halfGD



























end halfGD

/-! ### The two strategies are a controlled comparison

Both start at the origin and differ only in the step size, exactly as the
frozen implementation's docstring says.  A half step is a step of the doubled
smoothness constant. -/







end FullFormalization

open FullFormalization
open FullFormalization.GD

open scoped Gradient RealInnerProductSpace
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FullFormalization.GD.point_succ (o : Oracle E) (L : ℝ) (k : ℕ) :
    point o L (k + 1) = point o L k - (1 / L) • o.gradient (point o L k) := by sorry
