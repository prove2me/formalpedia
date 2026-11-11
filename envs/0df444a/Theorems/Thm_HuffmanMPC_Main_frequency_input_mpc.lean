-- Prove2me | Theorems.Thm_HuffmanMPC_Main_frequency_input_mpc
-- name    : HuffmanMPC.Main.frequency_input_mpc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:28:24.60542+00:00
-- url     : https://prove2.me/theorems/f33b9706-0e33-4108-a60a-778ad7171418
-- title:
--   Theorem 7.1 — Huffman coding from at most $m$ frequencies of total $n$
-- statement:
--   There are constants $c,k$ such that for every $0<\varepsilon<1$ some MPC program computes $\mu(f_1,\dots,f_r)$ for every $m\ge2$ and every list of $r\le m$ positive integer frequencies of total sum $n$, given the clipped size bound $m_*=\min\{m,\max\{2,n\}\}$ and the frequencies in arbitrary order, using at most
--   $$c\,\varepsilon^{-3}\Big(1+\frac{\log n}{\log m}\Big)\log(2+\log m)\ \text{rounds},\qquad c\,m^{\varepsilon}\log(2m)\ \text{local words},$$
--   $$c\,m^{1+\varepsilon}\varepsilon^{-2}\log^2(2m)\log(2+\log m)\ \text{total memory},\qquad c\,m^{1+\varepsilon}\varepsilon^{-3}\Big(1+\frac{\log n}{\log m}\Big)\log^2(2m)\log(2+\log m)\ \text{total work}.$$
--
--   Words have $k(\lfloor\log_2(2+n)\rfloor+1)$ bits. The resource bounds retain the original $m$. Positivity implies that clipping preserves the size bound. For $m>n\ge2$, running at $m_*=n$ changes the displayed round bound by at most a factor of two, and the other factors are monotone in $m$.
--
--   The size bound $m$ need not equal the number of frequencies; Theorem 3.1 applies this result with $m_0=\lceil n^{1-\varepsilon/2}\rceil+1$.
--
--   Differences from the source:
--   - encoding: a size bound $m\ge\max\{2,|A|\}$ and words of $O(\log n)$ bits → the supplied size word is $m_*=\min\{m,\max\{2,n\}\}$; words have $k(\lfloor\log_2(2+n)\rfloor+1)$ bits; the envelopes use the original $m$; reason: positive integer frequencies imply $|A|\le n$, so every source instance remains; clipping keeps the parameter in one source-sized word, with no restriction on the original bound
--   - reading: $O(\cdot)$ bounds with $\varepsilon$ shown explicitly → constants $c,k$ chosen before $\varepsilon$, uniform over $0<\varepsilon<1$; reason: the explicit $\varepsilon^{-2},\varepsilon^{-3}$ factors are meaningful only with $\varepsilon$-independent constants
--   - encoding: an MPC algorithm described in pseudo-code → existence of one program of the defined MPC machine whose actual execution on every legal input placement is correct and meets all four bounds; reason: the pseudo-code cannot be named in Lean; every operation (sorting, routing, scans) is charged in the execution
-- source:
--   Masoud Seddighin, Saeed Seddighin, Massively Parallel Algorithms for Huffman Coding, STOC 2027 submission #377 (October 2026), SHA-256 f63f78c8ea11dfeb34be181f681ce85dc9fd1fa2def1da4a30b231073a8166ba, Theorem 7.1, pp. 31–32 (PDF 32–33)

import Definitions.Def_HuffmanMPC_Main_Pipeline

set_option autoImplicit false

namespace HuffmanMPC.Main

/-- Theorem 7.1 (pp. 31–32): frequency input with size bound `m ≥ 2` and total `n`;
constants uniform in `ε`. -/
theorem frequency_input_mpc : ∃ (c : ℝ) (k : ℕ), 0 < c ∧ 0 < k ∧
    ∀ eps : ℝ, 0 < eps → eps < 1 → ∃ p : MPCProgram,
      ProgramSolves frequencyProblem (frequencyEnvelope eps) (fun _ => True) p c k := by sorry

end HuffmanMPC.Main
