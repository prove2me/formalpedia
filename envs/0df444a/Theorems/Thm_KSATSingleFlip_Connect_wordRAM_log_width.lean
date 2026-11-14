-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_wordRAM_log_width
-- name    : KSATSingleFlip.Connect.wordRAM_log_width
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:58:24.188111+00:00
-- url     : https://prove2.me/theorems/038d14fa-5b3b-4f08-bf9d-4ad816a64447
-- title:
--   Logarithmic word width for sparse k-SAT computations
-- statement:
--   For the candidate word-RAM model, if the sparse formula has $m\le cn$ clauses and the computation has at most $d(n+1)^2$ steps, then each of the two declared word widths is at most $$\log_2(k+c+2kc+d+13)+2\log_2(n+1)+5,$$ where the logarithms in this display are floor base-two logarithms. Thus for fixed $k,c,d$ the width is $O(\log n)$, ruling out unit-cost operations on superpolynomially large words in the intended linear and quadratic regimes. This statement concerns the model and does not prove an algorithm.
-- source:
--   Formalization choice for the runtime statements in Wang, Yin, Yu, Zhang, Single-Variable Connectivity in Random k-SAT, Theorem 1.3, printed p. 4 (PDF p. 6), STOC 2027 submission #737, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_WordRAM

namespace KSATSingleFlip.Connect

/-- Sparse linear input and quadratic budgets require logarithmic word width. -/
theorem wordRAM_log_width (n k m T c d : ℕ)
    (hm : m ≤ c * n) (hT : T ≤ d * (n + 1)^2) :
    wordRAMWidth n k m T ≤
      Nat.log2 (k + c + 2*k*c + d + 13) + 2 * Nat.log2 (n + 1) + 5 ∧
    wordRAMRouteWidth n k m T ≤
      Nat.log2 (k + c + 2*k*c + d + 13) + 2 * Nat.log2 (n + 1) + 5 := by
  sorry

end KSATSingleFlip.Connect
