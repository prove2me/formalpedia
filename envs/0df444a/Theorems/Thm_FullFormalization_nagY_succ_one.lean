-- Prove2me | Theorems.Thm_FullFormalization_nagY_succ_one
-- name    : FullFormalization.nagY_succ_one
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-09T05:51:55.838598+00:00
-- url     : https://prove2.me/theorems/444afbc3-bc5a-417f-97f0-dde6e421e3b1
-- title:
--   Gradient step at unit smoothness: $y_{k+1} = x_k - \nabla f(x_k)$
-- statement:
--   In the normalized setting $L = 1$ fixed in §1, the gradient step of the rational-momentum Nesterov method takes the unit-step form
--   $$ y_{k+1} \;=\; x_k \;-\; \nabla f(x_k), $$
--   for every function $f : E \to \mathbb{R}$, initial point $x_0$ and step index $k$, where $x_k$ is the extrapolated iterate and $\nabla f(x_k)$ the queried gradient. It is source (3.1) specialized to $L = 1$.
-- source:
--   《有理动量 Nesterov 紧界与半径归一化五算法共同最坏情形 — 可审计完整证明稿》 (manuscript, 2026-10-08), §3, eq. (3.1) specialized to $L = 1$ (§1 normalization, source lines 120-176); Lean: FullFormalization.RationalNAG lines 79-84

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
import Theorems.Thm_FullFormalization_nagY_succ

namespace FullFormalization

open scoped Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

























end FullFormalization

open FullFormalization

open scoped Gradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem FullFormalization.nagY_succ_one (f : E → ℝ) (x₀ : E) (k : ℕ) :
    nagY f 1 x₀ (k + 1) = nagX f 1 x₀ k - ∇ f (nagX f 1 x₀ k) := by sorry
