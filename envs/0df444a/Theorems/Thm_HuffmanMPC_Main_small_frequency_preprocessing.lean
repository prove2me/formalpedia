-- Prove2me | Theorems.Thm_HuffmanMPC_Main_small_frequency_preprocessing
-- name    : HuffmanMPC.Main.small_frequency_preprocessing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:28:05.811197+00:00
-- url     : https://prove2.me/theorems/9eefe72b-45b9-4c0e-b4e2-12ce5b1299d6
-- title:
--   Lemma 7.3 — small-frequency preprocessing in $O(\varepsilon^{-1})$ rounds
-- statement:
--   Fix $K$, which bounds the symbol size. There are constants $c,k,N$ such that for every $0<\varepsilon<1$ some MPC program does the following on every text $T$ of length $n$ with symbols below $(n+1)^K$. The preprocessing subroutine receives its threshold $\theta=\lceil n^\varepsilon\rceil$ as one charged parameter word. It outputs exactly the residual multiset and accumulated cost obtained by merging the two smallest frequencies while both are strictly less than $\theta$, retaining the final carry. In particular, it outputs a multiset $A_0$ of positive frequencies with sum $n$ and a cost $c_0$ such that:
--
--   1. the optimum encoded length of $T$ equals $c_0$ plus the optimum encoded length of $A_0$, $\mu(T)=c_0+\mu(A_0)$;
--   2. either $|A_0|\le1$ or the second-smallest frequency of $A_0$ is at least $\lceil n^\varepsilon\rceil$;
--   3. $|A_0|\le n^{1-\varepsilon}+1$.
--
--   For $n\ge N$ it uses at most
--   $$c\,\varepsilon^{-1}\ \text{rounds},\qquad c\,n^{\varepsilon}\ \text{local words},\qquad c\,n\,\varepsilon^{-1}\log(2n)\ \text{total memory and total work},$$
--   with words of $k(\lfloor\log_2(2+n)\rfloor+1)$ bits.
--
--   This lemma reduces the instance to $O(n^{1-\varepsilon})$ frequencies before the frequency-input algorithm is applied in Theorem 3.1.
--
--   Differences from the source:
--   - encoding: the counter-and-carry preprocessing procedure → one MPC program returning the exact Huffman prefix with operands strictly below the threshold, including its accumulated cost and residual multiset; reason: processing the counters in increasing order performs exactly this prefix; the threshold-minus-one specification retains the final carry and charges all parallel work
--   - reading: the preprocessing with threshold $\lceil n^\varepsilon\rceil$ → the subroutine receives this integer threshold as one charged input parameter, followed by the raw text; reason: Section 7 parameterizes the counter procedure by its threshold; this size-only parameter contains no symbol, frequency or optimum information, and avoids treating an arbitrary real power as a word instruction
--   - reading: $O(\varepsilon^{-1})$, $O(n^\varepsilon)$, $O(n\varepsilon^{-1}\log(2n))$ with $\varepsilon$ shown explicitly → constants $c,k,N$ chosen before $\varepsilon$, uniform over $0<\varepsilon<1$; reason: the explicit $\varepsilon$ factors in the bounds are meaningful only with $\varepsilon$-independent constants
--   - encoding: a text over a general alphabet with $O(\log n)$-bit words → symbols are naturals below $(n+1)^K$ for each fixed $K$; words of $k(\lfloor\log_2(2+n)\rfloor+1)$ bits; reason: this is exactly the class of $O(\log n)$-bit symbols
--   - encoding: asymptotic $O(\cdot)$ bounds → bounds for all $n\ge N$; correctness for every $n$, including $n=0$; reason: standard eventual reading of $O$
--   - generalization: outputs $A_0$ and $c_0$ with the three listed properties → also asserts $A_0$ positive with sum $n$; reason: merges preserve positivity and the total; Theorem 3.1's proof uses that the sum is still $n$; dropping the extra clauses gives the source statement
-- source:
--   Masoud Seddighin, Saeed Seddighin, Massively Parallel Algorithms for Huffman Coding, STOC 2027 submission #377 (October 2026), SHA-256 f63f78c8ea11dfeb34be181f681ce85dc9fd1fa2def1da4a30b231073a8166ba, Lemma 7.3, p. 35 (PDF 36)

import Definitions.Def_HuffmanMPC_Main_Pipeline

set_option autoImplicit false

namespace HuffmanMPC.Main

/-- Lemma 7.3 (p. 35): the preprocessing with threshold `⌈n^ε⌉`; constants uniform in `ε`. -/
theorem small_frequency_preprocessing : ∀ K : ℕ, ∃ (c : ℝ) (k N : ℕ), 0 < c ∧ 0 < k ∧
    ∀ eps : ℝ, 0 < eps → eps < 1 → ∃ p : MPCProgram,
      ProgramSolves (preprocessingProblem K eps) (preprocessingEnvelope eps)
        (fun n => N ≤ n) p c k := by sorry

end HuffmanMPC.Main
