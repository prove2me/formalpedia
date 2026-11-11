-- Prove2me | Theorems.Thm_HuffmanMPC_Main_exact_huffman_mpc
-- name    : HuffmanMPC.Main.exact_huffman_mpc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:28:37.772476+00:00
-- url     : https://prove2.me/theorems/5975b918-5488-47ac-a70a-205211669ccc
-- title:
--   Theorem 3.1 — exact optimal encoded length in $O_\varepsilon(\log\log n)$ MPC rounds with $\tilde O(n^\varepsilon)$ local and $\tilde O(n)$ total resources
-- statement:
--   Fix $K$, which bounds the symbol size. There are constants $c,k,N$ such that for every $\varepsilon>0$ some MPC program receives a text $T$ of length $n$, with symbols below $(n+1)^K$ and distributed arbitrarily over the machines, and outputs $\mu(T)$, the minimum encoded length over all prefix-free binary codes (zero when $T$ has at most one distinct symbol). Write $e=\varepsilon$ if $\varepsilon<1$ and $e=1/2$ otherwise. For $n\ge N$ the program uses at most
--   $$c\,e^{-3}\log(2+\log n)\ \text{rounds},\qquad c\,n^{\varepsilon}\log(2n)\ \text{words per machine},$$
--   and total memory and total work each at most
--   $$c\,n\,e^{-3}\log^2(2n)\log(2+\log n),$$
--   with words of $k(\lfloor\log_2(2+n)\rfloor+1)$ bits.
--
--   For $0<\varepsilon<1$ these are the explicit bounds of p. 36; for every $\varepsilon>0$ they give the introductory form: $O_\varepsilon(\log\log n)$ rounds, $\tilde O(n^\varepsilon)$ memory per machine, $\tilde O(n)$ total memory and computation.
--
--   Differences from the source:
--   - generalization: intro: for every $\varepsilon>0$, $O_\varepsilon(\log\log n)$ rounds, $\tilde O(n^\varepsilon)$ local, $\tilde O(n)$ total; explicit form for $0<\varepsilon<1$ → the explicit p. 36 bounds for every $\varepsilon>0$, with $\varepsilon^{-3}$ replaced by $2^3$ for $\varepsilon\ge1$; reason: implies both source forms; for $\varepsilon\ge1$ it is the $\varepsilon=1/2$ construction, whose local bound $n^{1/2}\log(2n)$ is at most $n^\varepsilon\log(2n)$
--   - reading: $O(\varepsilon^{-3}\cdots)$ bounds with $\varepsilon$ shown explicitly → constants $c,k,N$ chosen before $\varepsilon$, uniform over all $\varepsilon>0$; reason: the explicit $\varepsilon^{-3}$ factor is meaningful only with $\varepsilon$-independent constants
--   - encoding: a text over a general alphabet with $O(\log n)$-bit words → symbols are naturals below $(n+1)^K$ for each fixed $K$; words of $k(\lfloor\log_2(2+n)\rfloor+1)$ bits; reason: this is exactly the class of $O(\log n)$-bit symbols
--   - encoding: asymptotic $O(\cdot)$ bounds → bounds for all $n\ge N$; correctness for every $n$, including the empty and one-symbol texts; reason: standard eventual reading of $O$; the source handles $m=1$ with the empty codeword
--   - encoding: an MPC algorithm described in pseudo-code → existence of one program of the defined MPC machine whose actual execution on every legal input placement is correct and meets all four bounds; reason: the pseudo-code cannot be named in Lean; every operation (sorting, routing, scans) is charged in the execution
-- source:
--   Masoud Seddighin, Saeed Seddighin, Massively Parallel Algorithms for Huffman Coding, STOC 2027 submission #377 (October 2026), SHA-256 f63f78c8ea11dfeb34be181f681ce85dc9fd1fa2def1da4a30b231073a8166ba, Theorem 3.1, p. 3 (PDF 4); explicit restatement p. 36 (PDF 37), proof to p. 38 (PDF 39)

import Definitions.Def_HuffmanMPC_Main_Pipeline

set_option autoImplicit false

namespace HuffmanMPC.Main

/-- Theorem 3.1 (p. 3; explicit form p. 36): for every `ε > 0`, exact `μ(T)` for a raw
text of length `n`, with the four explicit bounds of p. 36 for all large `n`. -/
theorem exact_huffman_mpc : ∀ K : ℕ, ∃ (c : ℝ) (k N : ℕ), 0 < c ∧ 0 < k ∧
    ∀ eps : ℝ, 0 < eps → ∃ p : MPCProgram,
      ProgramSolves (textProblem K) (textEnvelope eps) (fun n => N ≤ n) p c k := by sorry

end HuffmanMPC.Main
