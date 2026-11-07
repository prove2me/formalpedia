-- Prove2me | Theorems.Thm_OnlineBudgetAlloc_eq_7
-- name    : OnlineBudgetAlloc.eq_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:35:44.525405+00:00
-- url     : https://prove2.me/theorems/fd2f55f4-61e7-4917-bf69-0f6f2870bd8f
-- title:
--   Display (7) — sums replaced by integrals, up to $+2$
-- statement:
--   Here $D_{N,d}$ is the paper's three-phase random input with $N$ unit-budget advertisers (§2), $H = N/e$, $M = 2N/3$ and $R = M(1-2/d)$; the standing assumptions of §2 are that $3 \mid N$, $d \ge 8$ is even, and $d \mid M$. The middle-phase partition into groups $A_i \cup B_i$ is arbitrary, and the statement holds for every choice.
--
--   **Display (7).** For every deterministic online algorithm on $D_{N,d}$,
--   $$
--   \mathbb E[\mathrm{ALG}] \le \frac{11H}{12} + \frac34\int_M^N \Bigl(1 - \frac{H}{x}\Bigr)dx + \Delta_{\mathrm{mid}} + \int_0^R F(x)\,dx + 2 .
--   $$
--
--   The two sums of display (5) are replaced by integrals, at a cost of at most $2$, because $1 - H/x \le 1$ and $F(x) \le 1$ are non-decreasing in $x$.
--
--   Differences from the source:
--   - encoding: the random input $D_{N,d}$, whose middle-phase partition is chosen arbitrarily → the uniform law on a finite seed type (removal orders, coins, removal positions), for every valid partition rule `part`; reason: the seed law gives each removal uniformly over the current remaining set (or half), independently of the algorithm, which is the paper's law; the statement holds for every admissible choice of the arbitrary partition
--   - encoding: §2's w.l.o.g. assumptions: $3 \mid N$, $d$ even, $d \ge 8$, $d \mid M$ → explicit hypotheses `3 ∣ N`, `Even d`, `8 ≤ d`, `d ∣ 2 * N / 3`; reason: they only exclude parameters for which $D_{N,d}$ is undefined
--   - encoding: $\int_0^R F(x)\,dx$ with $F$ undefined at $0$ → interval integral of `Fpot`, whose value at $0$ is Lean's $H/0 = 0$ junk; reason: a single point; it changes no integral
-- source:
--   Panigrahi, Zhang, The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e, arXiv:2610.41136 (held version, sha256 913d8f02…), §3.4, p.6, eq. (7)

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

/-- **Display (7)** (Panigrahi–Zhang, *The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e*, arXiv:2610.41136 (held version, sha256 913d8f02…), §3.4, p.6). For every deterministic online algorithm on `D_{N,d}`,
`E[ALG] ≤ 11H/12 + (3/4)∫_M^N (1 − H/x) dx + ∆_mid + ∫_0^R F(x) dx + 2`, with `H = N/e`,
`M = 2N/3`, `R = M(1 − 2/d)` and `F` as in (6).

**Formalization Note** The hypotheses `3 ∣ N`, `d` even, `8 ≤ d` and `d ∣ 2N/3` are the
"w.l.o.g." assumptions of §2 (p.2) under which `D_{N,d}` is defined. The partition of the middle
phase is "arbitrary" (p.2): the statement holds for every valid partition rule `part`. The integrals are interval integrals; `F(0)` is Lean's junk value at a single point. -/
theorem eq_7 {N d : ℕ} (hN : 3 ∣ N) (hd : Even d) (hd8 : 8 ≤ d) (hdM : d ∣ 2 * N / 3)
    (part : PartitionRule N d) (hpart : part.IsValid) (A : DetAlg N) :
    expD (fun s : Seed N d => A.alg (inputD part s)) ≤
      11 * Hscale N / 12 +
        3 / 4 * (∫ x in (numM N : ℝ)..(N : ℝ), (1 - Hscale N / x)) +
        deltaMid part A +
        (∫ x in (0 : ℝ)..(numR N d : ℝ), Fpot (Hscale N) x) + 2 := by sorry

end OnlineBudgetAlloc
