-- Prove2me | Theorems.Thm_HuffmanMPC_Main_Supplement_sorted_prefix_huffman_pram
-- name    : HuffmanMPC.Main.Supplement.sorted_prefix_huffman_pram
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:20:24.771161+00:00
-- url     : https://prove2.me/theorems/ba600d45-aedb-4852-9f77-d54364c772dd
-- title:
--   Theorem 9.2 — exact Huffman optimum from sorted prefixes; companion theorem
-- statement:
--   There are universal constants $c>0$ and an integer $k>0$ such that, for every fixed $0<\varepsilon<1$, one deterministic common-CRCW word program works for every sorted list $A$ of $m\ge2$ positive integer frequencies with total $n$. Its input is the supplied prefix array of $A$, with redundant length and total words, and its output is the independent minimum encoded length $\mu(A)$ over binary prefix-free codes.
--
--   Writing $\ell(m)=\max\{1,\log_2m\}$ and $\ell_2(m)=\max\{1,\log_2\ell(m)\}$, the same execution satisfies
--   $$\mathrm{time}\le c\varepsilon^{-2}\left(1+\frac{\log_2n}{\log_2m}\right)\ell_2(m),$$
--   $$\mathrm{work}\le c\varepsilon^{-2}\left(1+\frac{\log_2n}{\log_2m}\right)m^{1+\varepsilon}\ell(m)^4.$$
--   All words have $k(\lfloor\log_2(2+n)\rfloor+1)$ bits. No polynomial relation between $n$ and $m$ is assumed. This is a companion PRAM theorem, independent of the published MPC goal; neither correctness nor a resource estimate is assumed about the program.
--
--   Differences from the source:
--   - encoding: prefix sums of m sorted positive integer frequencies of total n are supplied → prefix array with redundant m and n header words, and the published independent optimum as output specification; reason: m is the array length and n its last prefix; no frequency ordering work or additional solution information is supplied
--   - reading: big-O bounds with the fixed parameter shown explicitly → positive constants c and k precede the parameter, sizes and input; reason: the explicit inverse-parameter factors and the proof estimates use uniform multipliers; no numerical multiplier is invented
--   - encoding: deterministic common-CRCW PRAM with O(log n)-bit words → finite word program, old-snapshot reads, agreeing writes, measured execution and k(floor(log2(2+n))+1)-bit words; reason: operationalizes the stated machine without aggregate or optimum instructions; parallel activation is charged per target with constant depth and no data computation
--   - encoding: asymptotic resource estimates with logarithmic factors at least one → the clamped base-two envelopes bound every admissible size; reason: changing a fixed log base changes only a uniform multiplier; bounded small cases are absorbed using the standing clamp
-- source:
--   Masoud Seddighin, Saeed Seddighin, STOC 2027 submission #377 (October 2026), Massively Parallel Algorithms for Huffman Coding, pp. 42–43 (PDF 43–44), Theorem 9.2

import Definitions.Def_HuffmanMPC_Main_Supplement_Bounds

set_option autoImplicit false

namespace HuffmanMPC.Main.Supplement

/-- Theorem 9.2, pp.42–43 (PDF 43–44). A companion to the published MPC goal.
The same deterministic common-CRCW execution computes the independent optimum
within both bounds, for arbitrary total n and every fixed 0 < eps < 1. -/
theorem sorted_prefix_huffman_pram : ∃ (c : ℝ) (k : ℕ), 0 < c ∧ 0 < k ∧
    ∀ eps : ℝ, 0 < eps → eps < 1 → ∃ P : Program,
      HuffmanGuarantee P c k eps := by sorry

end HuffmanMPC.Main.Supplement
