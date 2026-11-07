-- Prove2me | Theorems.Thm_OnlineBudgetAlloc_deterministic_bound
-- name    : OnlineBudgetAlloc.deterministic_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:33:41.885731+00:00
-- url     : https://prove2.me/theorems/91227d8b-b7a3-443a-9c24-aa43f59d71a3
-- title:
--   Deterministic bound on $D_{N,d}$ — $\mathbb E[\mathrm{ALG}] \le (1-1/e)\,\mathrm{OPT} - \varepsilon N + 2$
-- statement:
--   For an even $d \ge 8$ and $N$ with $3 \mid N$ and $d \mid 2N/3$, let $D_{N,d}$ be the paper's three-phase random input (§2), with an arbitrary partition of the middle phase.
--
--   **Theorem (deterministic form of Theorem 1).** There are an even $d \ge 8$ and a constant $\varepsilon > 0$ such that, for every such $N$, every partition and every deterministic online algorithm,
--   $$
--   \mathbb E_{D_{N,d}}[\mathrm{ALG}] \le \Bigl(1 - \frac1e\Bigr)\mathrm{OPT} - \varepsilon N + 2, \qquad \mathrm{OPT} = \frac{11N}{12}.
--   $$
--
--   This is the input distribution of §2, which "establishes the upper bound in Theorem 1 on the expected competitive ratio of any deterministic algorithm": display (9) combined with Lemma 8. Yao's principle then turns it into Theorem 1.
--
--   Differences from the source:
--   - reading: \"Theorem 1 now follows from Lemmas 7 and 8\" (no displayed deterministic bound) → the explicit bound (9) + Lemma 8: $\exists$ even $d \ge 8$, $\exists \varepsilon > 0$, $\mathbb E[\mathrm{ALG}] \le (1-1/e)\cdot 11N/12 - \varepsilon N + 2$; reason: this is the deterministic statement of §2's opening paragraph that Yao's principle turns into Theorem 1
--   - reading: $\mathrm{OPT}$ → its value $11N/12$; reason: Lemma 2: every input in the support of $D_{N,d}$ has $\mathrm{OPT} = 11N/12$, and the paper substitutes this value itself (proof of Lemma 7)
--   - encoding: the random input $D_{N,d}$, whose middle-phase partition is chosen arbitrarily → the uniform law on a finite seed type (removal orders, coins, removal positions), for every valid partition rule `part`; reason: the seed law gives each removal uniformly over the current remaining set (or half), independently of the algorithm, which is the paper's law; the statement holds for every admissible choice of the arbitrary partition
-- source:
--   Panigrahi, Zhang, The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e, arXiv:2610.41136 (held version, sha256 913d8f02…), §2, p.2 (opening paragraph); §3.4, pp.7–8 (eq. (9), Lemma 8, "Theorem 1 now follows from Lemmas 7 and 8")

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

/-- **The bound for deterministic algorithms on `D_{N,d}`** (Panigrahi–Zhang, *The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e*, arXiv:2610.41136 (held version, sha256 913d8f02…), §2, p.2: "We construct an
input distribution for any sufficiently large N that establishes the upper bound in Theorem 1 on
the expected competitive ratio of any deterministic algorithm"; p.8: "Theorem 1 now follows from
Lemmas 7 and 8", i.e. (9) with Lemma 8). There are an even `d ≥ 8` and an `ε > 0` such that, for
every `N` with `3 ∣ N` and `d ∣ 2N/3`, every valid partition rule and every deterministic online
algorithm, `E[ALG] ≤ (1 − 1/e)·OPT − εN + 2` on `D_{N,d}`, where `OPT = 11N/12` (Lemma 2).

**Formalization Note** `OPT` is written as its value `11N/12` on the support of `D_{N,d}`
(Lemma 2). `d` and `ε` are chosen before `N`. -/
theorem deterministic_bound :
    ∃ d : ℕ, Even d ∧ 8 ≤ d ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ N : ℕ, 3 ∣ N → d ∣ 2 * N / 3 →
        ∀ part : PartitionRule N d, part.IsValid → ∀ A : DetAlg N,
          expD (fun s : Seed N d => A.alg (inputD part s)) ≤
            (1 - 1 / Real.exp 1) * (11 * (N : ℝ) / 12) - ε * N + 2 := by sorry

end OnlineBudgetAlloc
