-- Prove2me | Theorems.Thm_OnlineBudgetAlloc_lemma_2
-- name    : OnlineBudgetAlloc.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:32:45.347031+00:00
-- url     : https://prove2.me/theorems/bc1530b7-44ca-46a1-a762-e4ac96002951
-- title:
--   Lemma 2 — every input in the support of $D_{N,d}$ has $\mathrm{OPT} = 11N/12$
-- statement:
--   Here $D_{N,d}$ is the paper's three-phase random input with $N$ unit-budget advertisers (§2), $H = N/e$, $M = 2N/3$ and $R = M(1-2/d)$; the standing assumptions of §2 are that $3 \mid N$, $d \ge 8$ is even, and $d \mid M$. The middle-phase partition into groups $A_i \cup B_i$ is arbitrary, and the statement holds for every choice.
--
--   **Lemma 2.** For every seed, the input of $D_{N,d}$ built from that seed has offline optimum
--   $$
--   \mathrm{OPT} = \frac{11N}{12}.
--   $$
--
--   This fixes the benchmark of the competitive ratio: every later bound on $\mathbb E[\mathrm{ALG}]$ is compared with $11N/12$.
--
--   Differences from the source:
--   - encoding: the random input $D_{N,d}$, whose middle-phase partition is chosen arbitrarily → the uniform law on a finite seed type (removal orders, coins, removal positions), for every valid partition rule `part`; reason: the seed law gives each removal uniformly over the current remaining set (or half), independently of the algorithm, which is the paper's law; the statement holds for every admissible choice of the arbitrary partition
--   - encoding: §2's w.l.o.g. assumptions: $3 \mid N$, $d$ even, $d \ge 8$, $d \mid M$ → explicit hypotheses `3 ∣ N`, `Even d`, `8 ≤ d`, `d ∣ 2 * N / 3`; reason: they only exclude parameters for which $D_{N,d}$ is undefined
-- source:
--   Panigrahi, Zhang, The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e, arXiv:2610.41136 (held version, sha256 913d8f02…), §3.1, p.3, Lemma 2

import Mathlib
import Definitions.Def_OnlineBudgetAlloc_Instance
import Definitions.Def_OnlineBudgetAlloc_revenue
import Definitions.Def_OnlineBudgetAlloc_opt
import Definitions.Def_OnlineBudgetAlloc_Seed
import Definitions.Def_OnlineBudgetAlloc_PartitionRule
import Definitions.Def_OnlineBudgetAlloc_inputD

namespace OnlineBudgetAlloc

/-- **Lemma 2** (Panigrahi–Zhang, *The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e*, arXiv:2610.41136 (held version, sha256 913d8f02…), §3.1, p.3). Every input in the support of `D_{N,d}` has
`OPT = 11N/12`.

**Formalization Note** The hypotheses `3 ∣ N`, `d` even, `8 ≤ d` and `d ∣ 2N/3` are the
"w.l.o.g." assumptions of §2 (p.2) under which `D_{N,d}` is defined. The partition of the middle
phase is "arbitrary" (p.2): the statement holds for every valid partition rule `part`. The support of `D_{N,d}` is the set of inputs `inputD part s` over all seeds `s`. -/
theorem lemma_2 {N d : ℕ} (hN : 3 ∣ N) (hd : Even d) (hd8 : 8 ≤ d) (hdM : d ∣ 2 * N / 3)
    (part : PartitionRule N d) (hpart : part.IsValid) (s : Seed N d) :
    opt (inputD part s) = 11 * (N : ℝ) / 12 := by sorry

end OnlineBudgetAlloc
