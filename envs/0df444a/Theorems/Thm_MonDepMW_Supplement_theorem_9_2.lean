-- Prove2me | Theorems.Thm_MonDepMW_Supplement_theorem_9_2
-- name    : MonDepMW.Supplement.theorem_9_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:34:25.308205+00:00
-- url     : https://prove2.me/theorems/f269d56c-0ff5-4d63-a3b7-314b68c22d25
-- title:
--   Theorem 9.2 — on translinear classes, merge sequences of radius-$r$ width $O_{\mathcal C,r}(\log^{12r+4} n)$ in $O_{\mathcal C,r}(n^3\log^2 n)$ time
-- statement:
--   Let $r\ge1$ and let $\mathcal C$ be a translinear class of graphs (Definition 9.1). Then there is an algorithm running in time
--
--   $$O_{\mathcal C,r}(n^3\log^2 n)$$
--
--   that, given an $n$-vertex graph $G\in\mathcal C$, constructs a merge sequence for $G$ of radius-$r$ width bounded by
--
--   $$O_{\mathcal C,r}\bigl(\log^{12r+4} n\bigr).$$
--
--   Since classes of bounded merge-width are translinear, this computes merge sequences of polylogarithmic width on every class of bounded merge-width.
--
--   **Formalization Note** The algorithm is a program of the published word RAM, chosen after $r$ and $\mathcal C$, correct at every word size $W\ge b(\lfloor\log_2(n+2)\rfloor+1)$; its input is $n$ and the adjacency matrix and its output is read by the mission's merge-sequence decoder. One constant $c$ (chosen after $\mathcal C$, $r$) serves both bounds: at most $c\,(n+1)^3\lfloor\log_2(n+2)\rfloor^2$ steps, and width at most $c\,\lfloor\log_2(n+2)\rfloor^{12r+4}$.
--
--   Differences from the source:
--
--   - encoding: O_{C,r}(n³ log² n) time → at most c·(n+1)³·⌊log₂(n+2)⌋² steps; reason: for n ≥ 2, ⌊log₂(n+2)⌋ lies between log₂(n)/2 and 2·log₂ n, so this is the same class of bounds; the shifts keep it positive at n ≤ 1
--   - encoding: radius-r width O_{C,r}(log^{12r+4} n) → width at most c·⌊log₂(n+2)⌋^{12r+4}, with the same c as the time bound; reason: same comparison of logarithms; one constant is the larger of two
--   - encoding: an algorithm → a program P with word-size factor b, chosen after r and C, on the published TrulySubcubicAPSP word RAM, input graphInput G, correct at every word size W ≥ b·(⌊log₂(n+2)⌋+1), output read by decodeMergeSeq, which must be a merge sequence for G (IsFor); reason: the RAM with words of length O(log n) (p.43) and the mission's fixed input/output layout
--   - encoding: r ∈ N → 1 ≤ r; reason: N is the positive integers (p.11)
--   - encoding: a graph class → MonDepMW.GraphClass (members on each Fin n); reason: every finite graph has a copy on some Fin n and all quantities are isomorphism invariant
-- source:
--   Dreier, Mählmann, Pilipczuk, Toruńczyk, Monadically Dependent Graph Classes Have Almost Bounded Merge-Width, arXiv:2611.06804 (held version, sha256 6e4b06082b6e92c2408f95cd60971cd454258095371878ae2f448416bdfeb60b), Theorem 9.2, p.35 (PDF p.37); Definition 9.1 p.34 (PDF 36)

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_WordRAM
import Definitions.Def_MonDepMW_RunsWithin
import Definitions.Def_MonDepMW_decodeSet
import Definitions.Def_MonDepMW_MergeSeq
import Definitions.Def_MonDepMW_Supplement_Translinear

set_option autoImplicit false

open TrulySubcubicAPSP

namespace MonDepMW.Supplement

/-- **Theorem 9.2.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded
Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), §9, p.35 (PDF p.37): "Let r ∈ N and C be a translinear
class of graphs. Then there exists an O_{C,r}(n³ log² n)-time algorithm that given an n-vertex graph G ∈ C, constructs a
merge sequence for G of radius-r width bounded by O_{C,r}(log^{12r+4} n)."

**Formalization Note.** `r ≥ 1` (`N` is the positive integers, p.11). Translinear is Definition 9.1
(`Translinear`). The program `P`, its word-size factor `b` and one constant `c` for both bounds are chosen after `r`
and `𝒞` and before `G`. `log n` is `⌊log₂(n + 2)⌋` (`Nat.log 2 (n + 2)`), which is at least `1` and within a factor `2`
of `log₂ n` for `n ≥ 2`, so the bounds do not vanish at `n ≤ 1` and are the paper's `O_{C,r}` bounds otherwise; `n³` is
`(n + 1)³` for the same reason. Input: `graphInput G` (`n`, then the adjacency matrix); the program must work at every
word size `W ≥ b · (⌊log₂(n + 2)⌋ + 1)` ("words of length O(log n)", p.43). Output: read by `decodeMergeSeq`; it must
be a merge sequence for `G` (`IsFor`) of radius-`r` width at most `c · ⌊log₂(n + 2)⌋^{12r+4}`. -/
theorem theorem_9_2 (r : ℕ) (hr : 1 ≤ r) (𝒞 : GraphClass) (h𝒞 : Translinear 𝒞) :
    ∃ (P : List Instr) (b c : ℕ),
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G ∈ 𝒞 n → ∀ W : ℕ, b * (Nat.log2 (n + 2) + 1) ≤ W →
        RunsWithin P W (c * (n + 1) ^ 3 * (Nat.log 2 (n + 2)) ^ 2) (graphInput G) fun out =>
          (decodeMergeSeq n out).IsFor G ∧
            (decodeMergeSeq n out).WidthLE r (c * (Nat.log 2 (n + 2)) ^ (12 * r + 4)) := by sorry

end MonDepMW.Supplement
