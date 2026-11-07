-- Prove2me | Theorems.Thm_OnlineBudgetAlloc_lemma_5
-- name    : OnlineBudgetAlloc.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:34:01.027234+00:00
-- url     : https://prove2.me/theorems/6e8cd7b4-ca2a-401e-80db-215d879c293f
-- title:
--   Lemma 5 — middle phase: $\mathbb E[\Delta_t + \Delta_{t+1} + \Delta_{t+2}] \le 2(1 - 11\alpha/12) - \alpha/24$
-- statement:
--   Here $D_{N,d}$ is the paper's three-phase random input with $N$ unit-budget advertisers (§2), $H = N/e$, $M = 2N/3$ and $R = M(1-2/d)$; the standing assumptions of §2 are that $3 \mid N$, $d \ge 8$ is even, and $d \mid M$. The middle-phase partition into groups $A_i \cup B_i$ is arbitrary, and the statement holds for every choice.
--
--   **Lemma 5.** Let $t, t+1, t+2$ be the three items of a group $g$ in the middle phase, and let $\alpha = H/M$. For every deterministic online algorithm,
--   $$
--   \mathbb E\bigl[\Delta_t + \Delta_{t+1} + \Delta_{t+2}\bigr] \le 2\Bigl(1 - \frac{11\alpha}{12}\Bigr) - \frac{\alpha}{24},
--   $$
--   where the expectation is over the random choice of which subgroup, $A_g$ or $B_g$, bids for item 3. The bound holds for every value of the rest of the randomness.
--
--   The $-\alpha/24$ is the gain over the classical analysis that drives the whole result.
--
--   Differences from the source:
--   - reading: the expectation is over the random choice of which subgroup bids for item 3 → the average over the two values of the coin of group $g$, with every other component of the seed fixed; reason: the paper's own sentence after (4); the conditional form, for every value of the rest of the seed, implies the unconditional expectation
--   - encoding: the random input $D_{N,d}$, whose middle-phase partition is chosen arbitrarily → the uniform law on a finite seed type (removal orders, coins, removal positions), for every valid partition rule `part`; reason: the seed law gives each removal uniformly over the current remaining set (or half), independently of the algorithm, which is the paper's law; the statement holds for every admissible choice of the arbitrary partition
--   - encoding: §2's w.l.o.g. assumptions: $3 \mid N$, $d$ even, $d \ge 8$, $d \mid M$ → explicit hypotheses `3 ∣ N`, `Even d`, `8 ≤ d`, `d ∣ 2 * N / 3`; reason: they only exclude parameters for which $D_{N,d}$ is undefined
-- source:
--   Panigrahi, Zhang, The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e, arXiv:2610.41136 (held version, sha256 913d8f02…), §3.3, p.5, Lemma 5, eq. (4)

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

/-- **Lemma 5** (Panigrahi–Zhang, *The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e*, arXiv:2610.41136 (held version, sha256 913d8f02…), §3.3, p.5, eq. (4)). Let items `t, t+1, t+2` be the items of group `g` in
the middle phase. Then `E[∆_t + ∆_{t+1} + ∆_{t+2}] ≤ 2(1 − 11α/12) − α/24`, where `α = H/M`,
`H = N/e`, `M = 2N/3`; the expectation is over the random choice of which subgroup bids for
item 3.

**Formalization Note** The expectation is over `coin g` only, with every other part of the seed
fixed: the left side is the average, over `coin g ∈ {true, false}`, of the three changes of
group `g`. This conditional form implies the unconditional one. The items of group `g` are
`midItem g 0, midItem g 1, midItem g 2`. The hypotheses `3 ∣ N`, `d` even, `8 ≤ d` and `d ∣ 2N/3` are the
"w.l.o.g." assumptions of §2 (p.2) under which `D_{N,d}` is defined. The partition of the middle
phase is "arbitrary" (p.2): the statement holds for every valid partition rule `part`. -/
theorem lemma_5 {N d : ℕ} (hN : 3 ∣ N) (hd : Even d) (hd8 : 8 ≤ d) (hdM : d ∣ 2 * N / 3)
    (part : PartitionRule N d) (hpart : part.IsValid) (A : DetAlg N)
    (s : Seed N d) (g : Fin (numGroups N d)) :
    (∑ c : Bool, ∑ k : Fin 3,
        deltaD part A { s with coin := Function.update s.coin g c } (midItem g k)) / 2 ≤
      2 * (1 - 11 * (Hscale N / (numM N : ℝ)) / 12) - Hscale N / (numM N : ℝ) / 24 := by sorry

end OnlineBudgetAlloc
