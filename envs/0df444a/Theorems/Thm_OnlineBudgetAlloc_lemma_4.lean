-- Prove2me | Theorems.Thm_OnlineBudgetAlloc_lemma_4
-- name    : OnlineBudgetAlloc.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:34:09.532548+00:00
-- url     : https://prove2.me/theorems/63091afd-0fd1-4b63-a71d-157551a2fd0b
-- title:
--   Lemma 4 — first phase: $\Delta_t \le \tfrac34(1 - H/s_t)$
-- statement:
--   Here $D_{N,d}$ is the paper's three-phase random input with $N$ unit-budget advertisers (§2), $H = N/e$, $M = 2N/3$ and $R = M(1-2/d)$; the standing assumptions of §2 are that $3 \mid N$, $d \ge 8$ is even, and $d \mid M$. The middle-phase partition into groups $A_i \cup B_i$ is arbitrary, and the statement holds for every choice.
--
--   **Lemma 4.** For every deterministic online algorithm, every seed, and every item $t$ arriving in the first phase,
--   $$
--   \Delta_t \le \frac34\Bigl(1 - \frac{H}{s_t}\Bigr),
--   $$
--   where $s_t$ is the number of remaining advertisers just before item $t$.
--
--   This bounds the change of the potential on each of the $N/3$ first-phase items.
--
--   Differences from the source:
--   - encoding: the random input $D_{N,d}$, whose middle-phase partition is chosen arbitrarily → the uniform law on a finite seed type (removal orders, coins, removal positions), for every valid partition rule `part`; reason: the seed law gives each removal uniformly over the current remaining set (or half), independently of the algorithm, which is the paper's law; the statement holds for every admissible choice of the arbitrary partition
--   - encoding: §2's w.l.o.g. assumptions: $3 \mid N$, $d$ even, $d \ge 8$, $d \mid M$ → explicit hypotheses `3 ∣ N`, `Even d`, `8 ≤ d`, `d ∣ 2 * N / 3`; reason: they only exclude parameters for which $D_{N,d}$ is undefined
-- source:
--   Panigrahi, Zhang, The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e, arXiv:2610.41136 (held version, sha256 913d8f02…), §3.3, p.5, Lemma 4

import Mathlib
import Definitions.Def_OnlineBudgetAlloc_Instance
import Definitions.Def_OnlineBudgetAlloc_revenue
import Definitions.Def_OnlineBudgetAlloc_DetAlg
import Definitions.Def_OnlineBudgetAlloc_Seed
import Definitions.Def_OnlineBudgetAlloc_PartitionRule
import Definitions.Def_OnlineBudgetAlloc_inputD
import Definitions.Def_OnlineBudgetAlloc_vcap
import Definitions.Def_OnlineBudgetAlloc_Hscale
import Definitions.Def_OnlineBudgetAlloc_deltaD
import Definitions.Def_OnlineBudgetAlloc_expD

namespace OnlineBudgetAlloc

/-- **Lemma 4** (Panigrahi–Zhang, *The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e*, arXiv:2610.41136 (held version, sha256 913d8f02…), §3.3, p.5). For every item `t` arriving in the first phase,
`∆_t ≤ (3/4)(1 − H/s_t)`, where `H = N/e` and `s_t` is the number of remaining advertisers just
before item `t`. The bound holds for every seed (pointwise, not only in expectation).

**Formalization Note** The hypotheses `3 ∣ N`, `d` even, `8 ≤ d` and `d ∣ 2N/3` are the
"w.l.o.g." assumptions of §2 (p.2) under which `D_{N,d}` is defined. The partition of the middle
phase is "arbitrary" (p.2): the statement holds for every valid partition rule `part`. First-phase item `k` is `firstItem d k`. -/
theorem lemma_4 {N d : ℕ} (hN : 3 ∣ N) (hd : Even d) (hd8 : 8 ≤ d) (hdM : d ∣ 2 * N / 3)
    (part : PartitionRule N d) (hpart : part.IsValid) (A : DetAlg N)
    (s : Seed N d) (k : Fin (numFirst N)) :
    deltaD part A s (firstItem d k) ≤
      3 / 4 * (1 - Hscale N / (numAlive part s (firstItem d k) : ℝ)) := by sorry

end OnlineBudgetAlloc
