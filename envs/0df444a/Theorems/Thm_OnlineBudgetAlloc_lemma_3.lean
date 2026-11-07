-- Prove2me | Theorems.Thm_OnlineBudgetAlloc_lemma_3
-- name    : OnlineBudgetAlloc.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:34:24.499817+00:00
-- url     : https://prove2.me/theorems/ddb822f9-f73a-4847-afad-f4143aeeeb93
-- title:
--   Lemma 3 (corrected: ≤ in place of =) — $\mathbb E[\mathrm{ALG}] \le 11H/12 + \sum_t \mathbb E[\Delta_t]$
-- statement:
--   Here $D_{N,d}$ is the paper's three-phase random input with $N$ unit-budget advertisers (§2), $H = N/e$, $M = 2N/3$ and $R = M(1-2/d)$; the standing assumptions of §2 are that $3 \mid N$, $d \ge 8$ is even, and $d \mid M$. The middle-phase partition into groups $A_i \cup B_i$ is arbitrary, and the statement holds for every choice.
--
--   **Lemma 3 (corrected).** For every deterministic online algorithm, its expected revenue on $D_{N,d}$ satisfies
--   $$
--   \mathbb E[\mathrm{ALG}] \le \frac{11H}{12} + \sum_t \mathbb E[\Delta_t],
--   $$
--   where the sum is over all items and $\Delta_t = p_t - (H/s_t)w_t$ is the change of the potential $\varphi(t) = \mathrm{ALG}_t + H\cdot\bar v_t$ on item $t$.
--
--   The paper prints this with "$=$". The equality fails: the last removal empties the remaining set, where $\bar v := 0$ by convention, so the potential drops by $H\cdot v(r)$ whenever the last advertiser keeps some budget. The inequality is what display (5) uses.
--
--   Differences from the source:
--   - correction: $\mathbb E[\mathrm{ALG}] = 11H/12 + \sum_t \mathbb E[\Delta_t]$ → $\mathbb E[\mathrm{ALG}] \le 11H/12 + \sum_t \mathbb E[\Delta_t]$; reason: the equality is false: for $N = 36$, $d = 8$ (all §2 assumptions hold) and the algorithm that never assigns an item, $\mathrm{ALG} = 0$ and every $\Delta_t = 0$, while $11H/12 = 33/e > 0$; the final removal empties the set ($\bar v := 0$) and only lowers $\varphi$
--   - encoding: the random input $D_{N,d}$, whose middle-phase partition is chosen arbitrarily → the uniform law on a finite seed type (removal orders, coins, removal positions), for every valid partition rule `part`; reason: the seed law gives each removal uniformly over the current remaining set (or half), independently of the algorithm, which is the paper's law; the statement holds for every admissible choice of the arbitrary partition
--   - encoding: §2's w.l.o.g. assumptions: $3 \mid N$, $d$ even, $d \ge 8$, $d \mid M$ → explicit hypotheses `3 ∣ N`, `Even d`, `8 ≤ d`, `d ∣ 2 * N / 3`; reason: they only exclude parameters for which $D_{N,d}$ is undefined
-- source:
--   Panigrahi, Zhang, The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e, arXiv:2610.41136 (held version, sha256 913d8f02…), §3.2, p.4, Lemma 3, eq. (2)

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

/-- **Lemma 3, corrected** (Panigrahi–Zhang, *The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e*, arXiv:2610.41136 (held version, sha256 913d8f02…), §3.2, p.4, eq. (2)). For every deterministic online algorithm,
the expected revenue on `D_{N,d}` satisfies `E[ALG] ≤ 11H/12 + ∑_t E[∆_t]`, with `H = N/e`.

The paper prints `=`; that is false: for the algorithm that never assigns an item, `ALG = 0` and
every `∆_t = 0`, while `11H/12 > 0` for `N ≥ 1`. The final removal empties the remaining set,
where `v̄ := 0` by convention, so it can only lower the potential. The inequality is what
display (5) uses.

**Formalization Note** The hypotheses `3 ∣ N`, `d` even, `8 ≤ d` and `d ∣ 2N/3` are the
"w.l.o.g." assumptions of §2 (p.2) under which `D_{N,d}` is defined. The partition of the middle
phase is "arbitrary" (p.2): the statement holds for every valid partition rule `part`. -/
theorem lemma_3 {N d : ℕ} (hN : 3 ∣ N) (hd : Even d) (hd8 : 8 ≤ d) (hdM : d ∣ 2 * N / 3)
    (part : PartitionRule N d) (hpart : part.IsValid) (A : DetAlg N) :
    expD (fun s : Seed N d => A.alg (inputD part s)) ≤
      11 * Hscale N / 12 +
        ∑ t : Fin (numItems N d), expD (fun s : Seed N d => deltaD part A s t) := by sorry

end OnlineBudgetAlloc
