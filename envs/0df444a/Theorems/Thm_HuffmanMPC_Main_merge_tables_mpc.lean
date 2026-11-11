-- Prove2me | Theorems.Thm_HuffmanMPC_Main_merge_tables_mpc
-- name    : HuffmanMPC.Main.merge_tables_mpc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:28:45.485202+00:00
-- url     : https://prove2.me/theorems/7681d58e-3680-47e8-a3ee-79c94d1f5813
-- title:
--   Lemma 5.5 — merging two budget tables in $O((1+\log_\eta|A|)(1+\log_\eta\min\{|A_1|,|A_2|\}))$ rounds
-- statement:
--   Consider an instance of size $m\ge2$ with ratio parameter $\lambda\ge1$ and its depth bounds $\ell,u$. Let $A_1,A_2$ be nonempty lists of positive frequencies with $|A_1|+|A_2|\le m$, and $A=A_1\uplus A_2$. Given the tables $\mu(A_1,b)$, $b\in\mathcal B(A_1)$, and $\mu(A_2,b)$, $b\in\mathcal B(A_2)$, distributed over the machines, Problem 3.2 asks for $\mu(A,b)$ for every $b\in\mathcal B(A)$ with a division $b=b_1+b_2$, $b_j\in\mathcal B(A_j)$, attaining it.
--
--   There are constants $c,k$ such that one MPC program, for every $\eta\ge2$, solves it with $\alpha=\log_\varphi2$ in at most
--   $$c\,(1+\log_\eta|A|)(1+\log_\eta\min\{|A_1|,|A_2|\})\ \text{rounds},\qquad c\,\eta\lambda^{2\alpha}\ \text{local words},$$
--   and total memory and total work each at most
--   $$c\,|A|\,\eta\,\lambda^{4\alpha}(1+\log_\eta|A|)^2\log(2|A|\eta\lambda).$$
--
--   This is the step that combines neighbouring tables in Algorithm 2.
--
--   Differences from the source:
--   - generalization: $A_1,A_2$ disjoint unions of consecutive blocks of the bounded-ratio instance → any nonempty positive lists with $|A_1|+|A_2|\le m$; reason: source instances are of this form; correctness and bounds involve only the tables, sizes, $\eta$ and $\lambda$
--   - reading: word size not fixed for this standalone subroutine (the source fixes $O(\log n)$-bit words only for frequency input, p. 31) → words of $k(\lfloor\log_2(2+N)\rfloor+1)$ bits, $N$ the index's scale, which bounds every number the instance stores; reason: a standalone table must hold its own indices, depths and costs; in the paper's invocation $N$ is polynomial in the frequency sum, so the width is the source's $O(\log n)$
--   - reading: $O(\cdot)$ bounds in $\eta,\lambda,|A|$ → one program and constants $c,k$ for all $m,\lambda,\eta$ and all instances; reason: these parameters appear inside the $O$-bounds
--   - encoding: the table for $A$ with its minimizing splits → records $(b,\mu(A,b),b_1,b_2)$ in any order; input tables as words $(\mathrm{tag},b,\mu)$; reason: a distributed table is a set of records
--   - encoding: an MPC algorithm described in pseudo-code → existence of one program of the defined MPC machine whose actual execution on every legal input placement is correct and meets all four bounds; reason: the pseudo-code cannot be named in Lean; every operation (sorting, routing, scans) is charged in the execution
-- source:
--   Masoud Seddighin, Saeed Seddighin, Massively Parallel Algorithms for Huffman Coding, STOC 2027 submission #377 (October 2026), SHA-256 f63f78c8ea11dfeb34be181f681ce85dc9fd1fa2def1da4a30b231073a8166ba, Problem 3.2 and Lemma 5.5, pp. 20, 22–23 (PDF 21, 23–24)

import Definitions.Def_HuffmanMPC_Main_Subroutines

set_option autoImplicit false

namespace HuffmanMPC.Main

/-- Lemma 5.5 (pp. 22–23): merging two child tables, with minimizing splits. -/
theorem merge_tables_mpc : SolvableMPC mergeProblem mergeEnvelope := by sorry

end HuffmanMPC.Main
