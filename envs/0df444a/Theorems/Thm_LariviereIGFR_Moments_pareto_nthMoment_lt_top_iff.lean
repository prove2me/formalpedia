-- Prove2me | Theorems.Thm_LariviereIGFR_Moments_pareto_nthMoment_lt_top_iff
-- name    : LariviereIGFR.Moments.pareto_nthMoment_lt_top_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:31:59.224147+00:00
-- url     : https://prove2.me/theorems/95ba159e-ca48-4af2-92d9-4d50f60c5cc8
-- title:
--   §3 preamble, p. 603 — the nth moment of Pareto(S, k) is finite iff k > n
-- statement:
--   Let $S>0$, $k>0$ and let $X_k$ be Pareto with scale $S$ and parameter $k$ (density $kS^k\xi^{-k-1}$ on $\xi\ge S$). For every real $n>0$,
--   $$
--   \mathbb E[X_k^n]<\infty\iff k>n .
--   $$
--
--   This is the moment fact the comparison argument of Theorem 2 rests on: the "if" direction bounds moments of laws whose generalized failure rate eventually exceeds $n$, the "only if" direction shows moments are infinite when it stays at or below $n$.
--
--   **Formalization Note** The paper states "the $n$th moment of $X_k$ is defined only if $k>n$"; its proof of Theorem 2 uses both directions, so the statement here is the equivalence, which contains the printed claim. The moment is the $[0,\infty]$-valued lower integral `nthMoment`.
-- source:
--   Lariviere, A note on probability distributions with increasing generalized failure rates, Oper. Res. 54(3) (2006), p. 603, §3 preamble

import Mathlib
import Definitions.Def_LariviereIGFR_Moments_Setting

namespace LariviereIGFR.Moments

open MeasureTheory ProbabilityTheory

/-- §3 preamble, p. 603: the `n`-th moment of a Pareto law with scale `S` and parameter `k` is finite
exactly when `k > n`. -/
theorem pareto_nthMoment_lt_top_iff (S k : ℝ) (hS : 0 < S) (hk : 0 < k) (n : ℝ) (hn : 0 < n) :
    nthMoment (paretoMeasure S k) n < ⊤ ↔ n < k := by sorry

end LariviereIGFR.Moments
