-- Prove2me | Theorems.Thm_OnlineBudgetAlloc_eq_5
-- name    : OnlineBudgetAlloc.eq_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:35:26.825963+00:00
-- url     : https://prove2.me/theorems/c7b8f040-a739-479a-9f70-7cdbfa87d748
-- title:
--   Display (5) — $\mathbb E[\mathrm{ALG}] \le 11H/12 + \sum_{s=M+1}^N \tfrac34(1-H/s) + \Delta_{\mathrm{mid}} + \sum_{s=1}^R F(s)$
-- statement:
--   Here $D_{N,d}$ is the paper's three-phase random input with $N$ unit-budget advertisers (§2), $H = N/e$, $M = 2N/3$ and $R = M(1-2/d)$; the standing assumptions of §2 are that $3 \mid N$, $d \ge 8$ is even, and $d \mid M$. The middle-phase partition into groups $A_i \cup B_i$ is arbitrary, and the statement holds for every choice.
--
--   **Display (5).** For every deterministic online algorithm on $D_{N,d}$,
--   $$
--   \mathbb E[\mathrm{ALG}] \le \frac{11H}{12} + \sum_{s=M+1}^{N} \frac34\Bigl(1 - \frac{H}{s}\Bigr) + \Delta_{\mathrm{mid}} + \sum_{s=1}^{R} F(s),
--   $$
--   where $\Delta_{\mathrm{mid}}$ is the total expected sum of $\Delta_t$ over the middle phase and $F$ is the function of display (6).
--
--   This combines Lemma 3 with the per-item bounds of Lemmas 4 and 6. In the first phase the items see $N, N-1, \dots, M+1$ remaining advertisers, and in the final phase $R, R-1, \dots, 1$.
--
--   Differences from the source:
--   - encoding: the random input $D_{N,d}$, whose middle-phase partition is chosen arbitrarily → the uniform law on a finite seed type (removal orders, coins, removal positions), for every valid partition rule `part`; reason: the seed law gives each removal uniformly over the current remaining set (or half), independently of the algorithm, which is the paper's law; the statement holds for every admissible choice of the arbitrary partition
--   - encoding: §2's w.l.o.g. assumptions: $3 \mid N$, $d$ even, $d \ge 8$, $d \mid M$ → explicit hypotheses `3 ∣ N`, `Even d`, `8 ≤ d`, `d ∣ 2 * N / 3`; reason: they only exclude parameters for which $D_{N,d}$ is undefined
-- source:
--   Panigrahi, Zhang, The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e, arXiv:2610.41136 (held version, sha256 913d8f02…), §3.4, p.6, eq. (5)

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
import Definitions.Def_OnlineBudgetAlloc_Fpot
import Definitions.Def_OnlineBudgetAlloc_deltaMid

namespace OnlineBudgetAlloc

/-- **Display (5)** (Panigrahi–Zhang, *The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e*, arXiv:2610.41136 (held version, sha256 913d8f02…), §3.4, p.6). For every deterministic online algorithm on `D_{N,d}`,
`E[ALG] ≤ 11H/12 + ∑_{s=M+1}^{N} (3/4)(1 − H/s) + ∆_mid + ∑_{s=1}^{R} F(s)`, with `H = N/e`,
`M = 2N/3`, `R = M(1 − 2/d)`, `F` as in (6) and `∆_mid` the total expected sum of `∆_t` over the
middle phase.

**Formalization Note** The hypotheses `3 ∣ N`, `d` even, `8 ≤ d` and `d ∣ 2N/3` are the
"w.l.o.g." assumptions of §2 (p.2) under which `D_{N,d}` is defined. The partition of the middle
phase is "arbitrary" (p.2): the statement holds for every valid partition rule `part`. -/
theorem eq_5 {N d : ℕ} (hN : 3 ∣ N) (hd : Even d) (hd8 : 8 ≤ d) (hdM : d ∣ 2 * N / 3)
    (part : PartitionRule N d) (hpart : part.IsValid) (A : DetAlg N) :
    expD (fun s : Seed N d => A.alg (inputD part s)) ≤
      11 * Hscale N / 12 +
        (∑ x ∈ Finset.Ioc (numM N) N, 3 / 4 * (1 - Hscale N / (x : ℝ))) +
        deltaMid part A +
        (∑ x ∈ Finset.Icc 1 (numR N d), Fpot (Hscale N) (x : ℝ)) := by sorry

end OnlineBudgetAlloc
