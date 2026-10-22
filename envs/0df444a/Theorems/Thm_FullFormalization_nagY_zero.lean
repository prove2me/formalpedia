-- Prove2me | Theorems.Thm_FullFormalization_nagY_zero
-- name    : FullFormalization.nagY_zero
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-09T05:34:15.076011+00:00
-- url     : https://prove2.me/theorems/3e574692-dcf0-49eb-a53e-e10b11c1df51
-- title:
--   Initial gradient-step iterate: $y_0 = x_0$
-- statement:
--   The two sequences of the rational-momentum Nesterov method start at the same point:
--   $$ y_0 \;=\; x_0, $$
--   for every function $f : E \to \mathbb{R}$, smoothness constant $L$ and initial point $x_{\mathrm{init}}$; here $y_k$ and $x_k$ are the gradient-step and extrapolated sequences of (3.1)-(3.2).
-- source:
--   《有理动量 Nesterov 紧界与半径归一化五算法共同最坏情形 — 可审计完整证明稿》 (manuscript, 2026-10-08), §3, algorithm statement, source lines 27-45 (initialization $y_0 = x_0$); Lean: FullFormalization.RationalNAG line 55

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

@[simp] theorem FullFormalization.nagY_zero (f : E → ℝ) (L : ℝ) (x₀ : E) : nagY f L x₀ 0 = x₀ := by sorry
