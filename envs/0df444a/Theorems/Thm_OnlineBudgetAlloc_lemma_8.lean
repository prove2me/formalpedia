-- Prove2me | Theorems.Thm_OnlineBudgetAlloc_lemma_8
-- name    : OnlineBudgetAlloc.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:35:32.590997+00:00
-- url     : https://prove2.me/theorems/d6157888-0d03-4d4e-97c8-a60dfffc1d00
-- title:
--   Lemma 8 — $\Delta_{\mathrm{mid}} - \int_R^M F < -\varepsilon N$ for large even $d$, and $\varepsilon = 1/(4320e)$ at $d = 90$
-- statement:
--   Let $H = N/e$, $M = 2N/3$, $R = M(1 - 2/d)$, and let $F$ be the function of display (6). $\Delta_{\mathrm{mid}}$ is the total expected change of the potential in the middle phase of $D_{N,d}$ for a deterministic online algorithm, with an arbitrary partition of the middle phase.
--
--   **Lemma 8.**
--   1. For every sufficiently large even constant $d$ there is a constant $\varepsilon > 0$, independent of $N$, such that for every $N \ge 1$ with $3 \mid N$ and $d \mid M$, every partition and every deterministic online algorithm,
--   $$
--   \Delta_{\mathrm{mid}} - \int_R^M F(x)\,dx < -\varepsilon N .
--   $$
--   2. For $d = 90$, the same holds with $\varepsilon = \dfrac{1}{4320e}$ (the paper's remark at the end of the proof).
--
--   Adding the middle phase lowers the bound of display (9) by a constant fraction of $\mathrm{OPT}$, which is the point of the construction.
--
--   Differences from the source:
--   - encoding: sufficiently large even $d$; $N$ under the §2 assumptions → $\exists d_0\ \forall d \ge d_0$ even; every $N \ge 1$ with `3 ∣ N` and `d ∣ 2 * N / 3`, every valid partition rule; reason: the §2 assumptions only exclude undefined parameters, and $N = 0$ makes both sides $0$
--   - encoding: the random input $D_{N,d}$, whose middle-phase partition is chosen arbitrarily → the uniform law on a finite seed type (removal orders, coins, removal positions), for every valid partition rule `part`; reason: the seed law gives each removal uniformly over the current remaining set (or half), independently of the algorithm, which is the paper's law; the statement holds for every admissible choice of the arbitrary partition
-- source:
--   Panigrahi, Zhang, The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e, arXiv:2610.41136 (held version, sha256 913d8f02…), §3.4, pp.7–8, Lemma 8 and the remark at the end of its proof

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

/-- **Lemma 8, with its remark for `d = 90`** (Panigrahi–Zhang, *The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e*, arXiv:2610.41136 (held version, sha256 913d8f02…), §3.4, pp.7–8).

1. For every sufficiently large even constant `d` there is a constant `ε > 0`, independent of `N`,
   such that `∆_mid − ∫_R^M F(x) dx < −εN` for every deterministic online algorithm on `D_{N,d}`.
2. "choosing d = 90, one can show the lemma statement for ε = 1/(4320e)" (p.8).

Here `M = 2N/3`, `R = M(1 − 2/d)` and `F` is (6) with `H = N/e`.

**Formalization Note** `ε` is chosen after `d` and before `N`, the partition rule and the
algorithm. The statement is for every `N ≥ 1` with `3 ∣ N` and `d ∣ 2N/3` (§2's "w.l.o.g."
assumptions; at `N = 0` both sides are `0`). For `d = 90` these say `135 ∣ N`. "Sufficiently large"
is `d ≥ d₀` for some `d₀`. -/
theorem lemma_8 :
    (∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → Even d → ∃ ε : ℝ, 0 < ε ∧
      ∀ N : ℕ, 3 ∣ N → d ∣ 2 * N / 3 → 0 < N →
        ∀ part : PartitionRule N d, part.IsValid → ∀ A : DetAlg N,
          deltaMid part A - (∫ x in (numR N d : ℝ)..(numM N : ℝ), Fpot (Hscale N) x) <
            -(ε * N)) ∧
    (∀ N : ℕ, 3 ∣ N → 90 ∣ 2 * N / 3 → 0 < N →
        ∀ part : PartitionRule N 90, part.IsValid → ∀ A : DetAlg N,
          deltaMid part A - (∫ x in (numR N 90 : ℝ)..(numM N : ℝ), Fpot (Hscale N) x) <
            -(1 / (4320 * Real.exp 1) * N)) := by sorry

end OnlineBudgetAlloc
