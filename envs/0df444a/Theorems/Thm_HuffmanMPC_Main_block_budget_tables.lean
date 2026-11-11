-- Prove2me | Theorems.Thm_HuffmanMPC_Main_block_budget_tables
-- name    : HuffmanMPC.Main.block_budget_tables
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:28:42.323435+00:00
-- url     : https://prove2.me/theorems/96befdb2-d9ba-401e-8d2f-4bf3170c2ebe
-- title:
--   Lemma 4.5 — the table of one block in $O(\log_\sigma b_{\max})$ MPC rounds
-- statement:
--   Let $B=(w_1,\dots,w_s)$ be a sorted block, $0<w_1\le\dots\le w_s\le\varphi w_1$, with depth bounds $1\le\ell\le u$, $s\le2^u$, and $b_{\max}=\min\{2^u,s2^{u-\ell}\}$. Problem 4.4 asks for $\mu(B,b)$ for every $b\in\{s,\dots,b_{\max}\}$.
--
--   There are constants $c,k$ such that one MPC program, for every $\sigma\ge2$, outputs for every such $b$ the value $\mu(B,b)$ together with an attaining assignment on three consecutive depths, using at most
--   $$c\max\{1,\log_\sigma b_{\max}\}\ \text{rounds},\qquad c\,\sigma\ \text{local words},\qquad c\,b_{\max}\max\{1,\log_\sigma b_{\max}\}\ \text{total memory},$$
--   $$c\,b_{\max}\big(\max\{1,\log_\sigma b_{\max}\}\max\{1,\log_2 b_{\max}\}+\max\{1,\log_2 u\}\big)\ \text{total work}.$$
--   As in the source, logarithms are taken to be at least one.
--
--   These tables initialize the bottom-up merging of Algorithm 2.
--
--   Differences from the source:
--   - generalization: a block of a bounded-ratio instance, with that instance's $\ell,u$ → any sorted $\varphi$-block and any $1\le\ell\le u$ with $s\le2^u$; reason: source blocks satisfy these conditions since $s\le m<2^u$
--   - generalization: compute $\mu(B,b)$ for every $b$ → also output the depth $h$ and counts $x,y,z$ of an attaining three-depth assignment; reason: Algorithm 1 stores them; forgetting them gives the source output
--   - reading: word size not fixed for this standalone subroutine (the source fixes $O(\log n)$-bit words only for frequency input, p. 31) → words of $k(\lfloor\log_2(2+N)\rfloor+1)$ bits, $N$ the index's scale, which bounds every number the instance stores; reason: a standalone table must hold its own indices, depths and costs; in the paper's invocation $N$ is polynomial in the frequency sum, so the width is the source's $O(\log n)$
--   - reading: $O(\cdot)$ bounds in $\sigma$ and $b_{\max}$ → one program and constants $c,k$ for all $\sigma\ge2$ and all instances; reason: $\sigma$ appears inside the $O$-bounds
--   - encoding: an MPC algorithm described in pseudo-code → existence of one program of the defined MPC machine whose actual execution on every legal input placement is correct and meets all four bounds; reason: the pseudo-code cannot be named in Lean; every operation (sorting, routing, scans) is charged in the execution
-- source:
--   Masoud Seddighin, Saeed Seddighin, Massively Parallel Algorithms for Huffman Coding, STOC 2027 submission #377 (October 2026), SHA-256 f63f78c8ea11dfeb34be181f681ce85dc9fd1fa2def1da4a30b231073a8166ba, Problem 4.4 and Lemma 4.5, pp. 15–16 (PDF 16–17)

import Definitions.Def_HuffmanMPC_Main_Subroutines

set_option autoImplicit false

namespace HuffmanMPC.Main

/-- Lemma 4.5 (p. 16): for every `σ ≥ 2`, Problem 4.4 in `O(log_σ b_max)` rounds with
`O(σ)` local words, `O(b_max log_σ b_max)` total memory and
`O(b_max (log_σ b_max log b_max + log u))` total work; constants uniform in `σ`. -/
theorem block_budget_tables : SolvableMPC blockProblem blockEnvelope := by sorry

end HuffmanMPC.Main
