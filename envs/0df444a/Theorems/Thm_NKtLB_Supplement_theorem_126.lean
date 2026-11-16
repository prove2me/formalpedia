-- Prove2me | Theorems.Thm_NKtLB_Supplement_theorem_126
-- name    : NKtLB.Supplement.theorem_126
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:48:06.895888+00:00
-- url     : https://prove2.me/theorems/c05d539c-01e0-4c66-882c-c64b7fd00389
-- title:
--   Theorem 126 — pseudodeterministic constructions for dense $\mathsf{pr}\text{-}\mathsf{BPP}^O$ properties, $O\in\mathsf{PSPACE}$
-- statement:
--   Let $O\in\mathsf{PSPACE}$, let $P=(\mathrm{YES},\mathrm{NO})$ be a promise problem in $\mathsf{pr}\text{-}\mathsf{BPP}^O$ whose YES part is dense, and let $\gamma>0$. Then there is an **infinitely-often pseudodeterministic explicit construction** for $P$ running in time $2^{n^\gamma}$ with oracle access to $O$ and $n^\gamma$ bits of advice. That is, there are a randomized oracle algorithm $A$ and advice strings $a_n\in\{0,1\}^{\lceil n^\gamma\rceil}$ such that for infinitely many $n$ some string $x_n\in\{0,1\}^n\setminus\mathrm{NO}$ satisfies
--   $$
--   \Pr_{r}\bigl[\,A^O(1^n,a_n;r)\text{ outputs }x_n\text{ within }2^{n^\gamma}\text{ steps}\,\bigr]\ \ge\ \frac23 .
--   $$
--
--   Footnote 26 of the paper: "if $P=(\mathrm{YES}_n,\mathrm{NO}_n)$, then there are infinitely many values of $n$ such that we can pseudodeterministically construct in subexponential time with a small amount of advice a string $x_n\notin\mathrm{NO}_n$". A language is dense if $|L\cap\{0,1\}^n|\ge 2^n/n^b$ for some $b>0$ and all large $n$ (p.12). The paper uses this result to show how a non-adaptive variant would refute symmetry of information for $rn\mathrm{Kt}$.
--
--   Differences from the source:
--   - reading: runs in time $2^{n^\gamma}$ with $n^\gamma$ bits of advice → halts within exactly $\lceil 2^{n^\gamma}\rceil$ steps with advice of exactly $\lceil n^\gamma\rceil$ bits, random string of length $\lceil 2^{n^\gamma}\rceil$; reason: the strictest reading of the bounds; $x_n$ has length $n$ as in footnote 26
--   - reading: $\mathsf{PSPACE}$ and $\mathsf{pr}\text{-}\mathsf{BPP}^O$ on an unspecified model → defined on the base `Machine` (polynomial space with bounded heads; error $1/3$ in time $c|x|^k+c$); reason: standard classes, not defined in the paper
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Appendix B, Theorem 126 and footnote 26, p.98

import Mathlib
import Definitions.Def_NKtLB_Supplement_PSPACE
import Definitions.Def_NKtLB_Supplement_PrBPP
import Definitions.Def_NKtLB_Dense
import Definitions.Def_NKtLB_prob

namespace NKtLB.Supplement

/-- **Theorem 126 (pseudodeterministic constructions for dense `pr-BPP^O` properties)** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026),
Appendix B, Theorem 126 and footnote 26, p.98): "For any `O ∈ PSPACE`, any dense `pr-BPP^O` property
`P`, and any `γ > 0`, there exists an infinitely-often pseudodeterministic explicit construction for
`P` that runs in time `2^{n^γ}`, given oracle access to `O` and `n^γ` bits of advice. [26: In other
words, if `P = (YES_n, NO_n)`, then there are infinitely many values of `n` such that we can
pseudodeterministically construct in subexponential time with a small amount of advice a string
`x_n ∉ NO_n`.]"

There are a machine `A` and advice strings `a_n` of length `⌈n^γ⌉` such that for infinitely many `n`
some `x_n ∈ {0,1}^n \ NO` is output by `A^O(1^n, a_n; r)` within `⌈2^{n^γ}⌉` steps with probability
at least `2/3` over `r ∈ {0,1}^{⌈2^{n^γ}⌉}` (one canonical output with probability `≥ 2/3`).

**Formalization Note.** Dense is the base `Dense` applied to `YES` (p.12). Input `1^n` on the input
tape, advice on the auxiliary tape, randomness on the randomness tape. The statement involves no
universal machine. -/
theorem theorem_126 :
    ∀ O : Set (List Bool), O ∈ PSPACE → ∀ P : Set (List Bool) × Set (List Bool), P ∈ PrBPP O →
      Dense P.1 → ∀ γ : ℝ, 0 < γ →
      ∃ (A : Machine) (a : ℕ → List Bool), (∀ n : ℕ, (a n).length = ⌈(n : ℝ) ^ γ⌉₊) ∧
        ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ x : List Bool, x.length = n ∧ x ∉ P.2 ∧
          (2 / 3 : ℝ) ≤ prob ⌈(2 : ℝ) ^ ((n : ℝ) ^ γ)⌉₊ (fun r =>
            A.HaltsWith O ⟨List.replicate n true, a n, [], r⟩ ⌈(2 : ℝ) ^ ((n : ℝ) ^ γ)⌉₊
              (bitsSym x)) := by sorry

end NKtLB.Supplement
