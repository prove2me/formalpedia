-- Prove2me | Theorems.Thm_OnlineBudgetAlloc_lemma_6
-- name    : OnlineBudgetAlloc.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:34:11.074866+00:00
-- url     : https://prove2.me/theorems/b283b592-3a1e-4983-b61f-1493d3e51835
-- title:
--   Lemma 6 — final phase: $\Delta_t \le \tfrac34(1 - H/s_t)_+ + \tfrac14(1 - \tfrac23 H/s_t)_+$
-- statement:
--   Here $D_{N,d}$ is the paper's three-phase random input with $N$ unit-budget advertisers (§2), $H = N/e$, $M = 2N/3$ and $R = M(1-2/d)$; the standing assumptions of §2 are that $3 \mid N$, $d \ge 8$ is even, and $d \mid M$. The middle-phase partition into groups $A_i \cup B_i$ is arbitrary, and the statement holds for every choice.
--
--   **Lemma 6.** For every deterministic online algorithm, every seed, and every item $t$ arriving in the final phase,
--   $$
--   \Delta_t \le \frac34\Bigl(1 - \frac{H}{s_t}\Bigr)_+ + \frac14\Bigl(1 - \frac23\cdot\frac{H}{s_t}\Bigr)_+, \qquad z_+ = \max\{z, 0\},
--   $$
--   where $s_t$ is the number of remaining advertisers just before item $t$. The right side is $F(s_t)$ of display (6).
--
--   Differences from the source:
--   - encoding: the random input $D_{N,d}$, whose middle-phase partition is chosen arbitrarily → the uniform law on a finite seed type (removal orders, coins, removal positions), for every valid partition rule `part`; reason: the seed law gives each removal uniformly over the current remaining set (or half), independently of the algorithm, which is the paper's law; the statement holds for every admissible choice of the arbitrary partition
--   - encoding: §2's w.l.o.g. assumptions: $3 \mid N$, $d$ even, $d \ge 8$, $d \mid M$ → explicit hypotheses `3 ∣ N`, `Even d`, `8 ≤ d`, `d ∣ 2 * N / 3`; reason: they only exclude parameters for which $D_{N,d}$ is undefined
-- source:
--   Panigrahi, Zhang, The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e, arXiv:2610.41136 (held version, sha256 913d8f02…), §3.3, p.6, Lemma 6

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

/-- **Lemma 6** (Panigrahi–Zhang, *The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e*, arXiv:2610.41136 (held version, sha256 913d8f02…), §3.3, p.6). For every item `t` arriving in the final phase,
`∆_t ≤ (3/4)(1 − H/s_t)₊ + (1/4)(1 − (2/3)·H/s_t)₊`, where `z₊ = max(z, 0)`, `H = N/e`, and `s_t`
is the number of remaining advertisers just before item `t`. The bound holds for every seed.

**Formalization Note** The hypotheses `3 ∣ N`, `d` even, `8 ≤ d` and `d ∣ 2N/3` are the
"w.l.o.g." assumptions of §2 (p.2) under which `D_{N,d}` is defined. The partition of the middle
phase is "arbitrary" (p.2): the statement holds for every valid partition rule `part`. Final-phase item `u` is `finalItem u`. -/
theorem lemma_6 {N d : ℕ} (hN : 3 ∣ N) (hd : Even d) (hd8 : 8 ≤ d) (hdM : d ∣ 2 * N / 3)
    (part : PartitionRule N d) (hpart : part.IsValid) (A : DetAlg N)
    (s : Seed N d) (u : Fin (numR N d)) :
    deltaD part A s (finalItem u) ≤
      3 / 4 * max (1 - Hscale N / (numAlive part s (finalItem u) : ℝ)) 0 +
        1 / 4 * max (1 - 2 / 3 * (Hscale N / (numAlive part s (finalItem u) : ℝ))) 0 := by sorry

end OnlineBudgetAlloc
