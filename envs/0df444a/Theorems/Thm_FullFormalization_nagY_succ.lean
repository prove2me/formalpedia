-- Prove2me | Theorems.Thm_FullFormalization_nagY_succ
-- name    : FullFormalization.nagY_succ
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-09T05:36:41.87663+00:00
-- url     : https://prove2.me/theorems/2e7ffc7b-de9c-4c90-ac05-d33fb5297fc4
-- title:
--   Gradient step: $y_{k+1} = x_k - \tfrac{1}{L}\nabla f(x_k)$
-- statement:
--   For an arbitrary function $f : E \to \mathbb{R}$, smoothness constant $L$, initial point $x_0$ and step index $k$, the gradient-step sequence of the rational-momentum Nesterov method is
--   $$ y_{k+1} \;=\; x_k \;-\; \frac{1}{L}\,\nabla f(x_k), $$
--   where $x_k$ is the extrapolated iterate, $\nabla f(x_k)$ the gradient queried at $x_k$, and $1/L$ the inverse of the smoothness constant. This is source (3.1).
-- source:
--   《有理动量 Nesterov 紧界与半径归一化五算法共同最坏情形 — 可审计完整证明稿》 (manuscript, 2026-10-08), §3, eq. (3.1); Lean: FullFormalization.RationalNAG lines 57-59

-- Generated from F:/20261008/FullFormalization\FullFormalization\RationalNAG.lean (Phase 3): skeleton subtraction, proof cut at
-- valStart (Stage 2), docstring stripped, declaration hoisted to top
-- level with its fully dotted name; body is `:= by sorry`.
/-
  FullFormalization.RationalNAG

  The rational-momentum Nesterov method, source section 3.

  Source lines 27-45 and 285-310:

      y_0 = x_0
      y_{k+1} = x_k - (1/L) ∇f(x_k)
      x_{k+1} = y_{k+1} + m_k (y_{k+1} - y_k),   m_k = k/(k+3),   k = 0, ..., N-1

  and the reported output is the **final extrapolated point `x_N`**
  (source line 46, emphasised).  This module defines exactly that two-sequence
  method and records the three relations (3.1), (3.2), (3.3) verbatim.

  There is no off-by-one shift anywhere: `nagX f L x₀ k` is `x_k` and
  `nagY f L x₀ k` is `y_k`, both indexed from `0`, and `nagPair … 0 = (x₀, x₀)`
  encodes `y_0 = x_0`.

  The proof variable `g_N = ∇f(x_N)` of source lines 312-319 is *not* part of
  this definition: the algorithm performs no gradient query at its output
  point.  `g_N` appears only inside `Certificate.lean`, as a free variable.
-/

import Mathlib
import Definitions.Def_Coefficients
import Definitions.Def_FunctionClass
import Definitions.Def_RationalNAG

namespace FullFormalization

open scoped Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

























end FullFormalization

open FullFormalization

open scoped Gradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem FullFormalization.nagY_succ (f : E → ℝ) (L : ℝ) (x₀ : E) (k : ℕ) :
    nagY f L x₀ (k + 1) = nagX f L x₀ k - (1 / L) • ∇ f (nagX f L x₀ k) := by sorry
