-- Prove2me | Theorems.Thm_OnlineBudgetAlloc_eq_9
-- name    : OnlineBudgetAlloc.eq_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:35:26.769697+00:00
-- url     : https://prove2.me/theorems/48f314ba-545d-4407-a5ee-25825366c527
-- title:
--   Display (9) — $\mathbb E[\mathrm{ALG}] \le (1-1/e)\,\mathrm{OPT} + \Delta_{\mathrm{mid}} - \int_R^M F + 2$
-- statement:
--   Here $D_{N,d}$ is the paper's three-phase random input with $N$ unit-budget advertisers (§2), $H = N/e$, $M = 2N/3$ and $R = M(1-2/d)$; the standing assumptions of §2 are that $3 \mid N$, $d \ge 8$ is even, and $d \mid M$. The middle-phase partition into groups $A_i \cup B_i$ is arbitrary, and the statement holds for every choice.
--
--   **Display (9).** For every deterministic online algorithm on $D_{N,d}$,
--   $$
--   \mathbb E[\mathrm{ALG}] \le \Bigl(1 - \frac1e\Bigr)\mathrm{OPT} + \Delta_{\mathrm{mid}} - \int_R^M F(x)\,dx + 2, \qquad \mathrm{OPT} = \frac{11N}{12}.
--   $$
--
--   This is Lemma 7 applied to display (7). It reduces the theorem to showing that $\Delta_{\mathrm{mid}}$ is smaller than the integral $\int_R^M F$ it replaces.
--
--   Differences from the source:
--   - reading: $\mathrm{OPT}$ → its value $11N/12$; reason: Lemma 2: every input in the support of $D_{N,d}$ has $\mathrm{OPT} = 11N/12$, and the paper substitutes this value itself (proof of Lemma 7)
--   - encoding: the random input $D_{N,d}$, whose middle-phase partition is chosen arbitrarily → the uniform law on a finite seed type (removal orders, coins, removal positions), for every valid partition rule `part`; reason: the seed law gives each removal uniformly over the current remaining set (or half), independently of the algorithm, which is the paper's law; the statement holds for every admissible choice of the arbitrary partition
--   - encoding: §2's w.l.o.g. assumptions: $3 \mid N$, $d$ even, $d \ge 8$, $d \mid M$ → explicit hypotheses `3 ∣ N`, `Even d`, `8 ≤ d`, `d ∣ 2 * N / 3`; reason: they only exclude parameters for which $D_{N,d}$ is undefined
-- source:
--   Panigrahi, Zhang, The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e, arXiv:2610.41136 (held version, sha256 913d8f02…), §3.4, p.7, eq. (9)

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

/-- **Display (9)** (Panigrahi–Zhang, *The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e*, arXiv:2610.41136 (held version, sha256 913d8f02…), §3.4, p.7). For every deterministic online algorithm on `D_{N,d}`,
`E[ALG] ≤ (1 − 1/e)·OPT + ∆_mid − ∫_R^M F(x) dx + 2`, with `M = 2N/3`, `R = M(1 − 2/d)`, `F` as in
(6) with `H = N/e`, and `OPT = 11N/12` (Lemma 2: the value of `OPT` on every input of the
support).

**Formalization Note** The hypotheses `3 ∣ N`, `d` even, `8 ≤ d` and `d ∣ 2N/3` are the
"w.l.o.g." assumptions of §2 (p.2) under which `D_{N,d}` is defined. The partition of the middle
phase is "arbitrary" (p.2): the statement holds for every valid partition rule `part`. -/
theorem eq_9 {N d : ℕ} (hN : 3 ∣ N) (hd : Even d) (hd8 : 8 ≤ d) (hdM : d ∣ 2 * N / 3)
    (part : PartitionRule N d) (hpart : part.IsValid) (A : DetAlg N) :
    expD (fun s : Seed N d => A.alg (inputD part s)) ≤
      (1 - 1 / Real.exp 1) * (11 * (N : ℝ) / 12) + deltaMid part A -
        (∫ x in (numR N d : ℝ)..(numM N : ℝ), Fpot (Hscale N) x) + 2 := by sorry

end OnlineBudgetAlloc
