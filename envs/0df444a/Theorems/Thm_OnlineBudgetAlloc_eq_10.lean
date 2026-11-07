-- Prove2me | Theorems.Thm_OnlineBudgetAlloc_eq_10
-- name    : OnlineBudgetAlloc.eq_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:36:07.458459+00:00
-- url     : https://prove2.me/theorems/66c453be-6982-4ade-b817-80d920b9586f
-- title:
--   Display (10) — $\Delta_{\mathrm{mid}} \le (M/d)\bigl(2(1 - 11H/(12M)) - H/(24M)\bigr)$
-- statement:
--   Here $D_{N,d}$ is the paper's three-phase random input with $N$ unit-budget advertisers (§2), $H = N/e$, $M = 2N/3$ and $R = M(1-2/d)$; the standing assumptions of §2 are that $3 \mid N$, $d \ge 8$ is even, and $d \mid M$. The middle-phase partition into groups $A_i \cup B_i$ is arbitrary, and the statement holds for every choice.
--
--   **Display (10).** For every deterministic online algorithm on $D_{N,d}$, the total expected change of the potential in the middle phase satisfies
--   $$
--   \Delta_{\mathrm{mid}} \le \frac{M}{d}\Bigl(2\Bigl(1 - \frac{11H}{12M}\Bigr) - \frac{H}{24M}\Bigr).
--   $$
--
--   This is Lemma 5 summed over the $M/d$ groups, with $\alpha = H/M$.
--
--   Differences from the source:
--   - encoding: the random input $D_{N,d}$, whose middle-phase partition is chosen arbitrarily → the uniform law on a finite seed type (removal orders, coins, removal positions), for every valid partition rule `part`; reason: the seed law gives each removal uniformly over the current remaining set (or half), independently of the algorithm, which is the paper's law; the statement holds for every admissible choice of the arbitrary partition
--   - encoding: §2's w.l.o.g. assumptions: $3 \mid N$, $d$ even, $d \ge 8$, $d \mid M$ → explicit hypotheses `3 ∣ N`, `Even d`, `8 ≤ d`, `d ∣ 2 * N / 3`; reason: they only exclude parameters for which $D_{N,d}$ is undefined
-- source:
--   Panigrahi, Zhang, The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e, arXiv:2610.41136 (held version, sha256 913d8f02…), §3.4, p.7, eq. (10)

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
import Definitions.Def_OnlineBudgetAlloc_deltaMid

namespace OnlineBudgetAlloc

/-- **Display (10)** (Panigrahi–Zhang, *The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e*, arXiv:2610.41136 (held version, sha256 913d8f02…), §3.4, p.7). For every deterministic online algorithm on `D_{N,d}`,
the total expected change of the potential in the middle phase satisfies
`∆_mid ≤ (M/d)(2(1 − 11H/(12M)) − H/(24M))`, with `H = N/e` and `M = 2N/3`.

**Formalization Note** The hypotheses `3 ∣ N`, `d` even, `8 ≤ d` and `d ∣ 2N/3` are the
"w.l.o.g." assumptions of §2 (p.2) under which `D_{N,d}` is defined. The partition of the middle
phase is "arbitrary" (p.2): the statement holds for every valid partition rule `part`. -/
theorem eq_10 {N d : ℕ} (hN : 3 ∣ N) (hd : Even d) (hd8 : 8 ≤ d) (hdM : d ∣ 2 * N / 3)
    (part : PartitionRule N d) (hpart : part.IsValid) (A : DetAlg N) :
    deltaMid part A ≤
      (numM N : ℝ) / d *
        (2 * (1 - 11 * Hscale N / (12 * (numM N : ℝ))) - Hscale N / (24 * (numM N : ℝ))) := by sorry

end OnlineBudgetAlloc
