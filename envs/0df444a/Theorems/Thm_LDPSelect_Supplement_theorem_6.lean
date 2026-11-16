-- Prove2me | Theorems.Thm_LDPSelect_Supplement_theorem_6
-- name    : LDPSelect.Supplement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:06:44.053243+00:00
-- url     : https://prove2.me/theorems/0c9a74d2-8462-45e9-aec8-1cad50727dff
-- title:
--   Theorem 6 — sharp multi-selection: the ratio is $(1+o(1))\,ak/n$ for $W^{\mathrm N}_k$ and $W^{\mathrm I}_k$
-- statement:
--   Let $n\to\infty$ with $1\le k\le n$ and $1\le a<\infty$ possibly depending on $n$, and suppose $ak/n\to0$. Write $M_k=\mathbb E[\text{sum of the }k\text{ largest values}]$. Then
--
--   1. $\displaystyle\inf_X\frac{W^{\mathrm N}_k(X)}{M_k(X)}=(1+o(1))\frac{ak}{n}$;
--   2. the same holds for $W^{\mathrm I}_k$;
--   3. the lower bound is achieved asymptotically by a fixed binary randomized-response mechanism: there are $\varepsilon_n\to0$ such that, for all large $n$ and every product prior, some non-interactive mechanism in which user $i$ reports one bit with $\Pr(Z_i=1\mid X_i=x)=(1+(a-1)\varphi_i(x))/(a+1)$ earns at least $(1-\varepsilon_n)\frac{ak}{n}M_k$ while selecting at most $k$ users.
--
--   So the private optimum captures, to leading order, an $ak/n$ fraction of the prophet's value, and interaction does not change the leading order.
--
--   **Formalization Note** $k$ and $a$ are functions of $n$, with the hypotheses required only for large $n$. The statement $(1+o(1))\,ak/n$ is that the ratio divided by $ak/n$ tends to $1$. The explicit finite-$n$ error bound mentioned in the paper is Theorem 18, a separate item of this mission.
--
--   Differences from the source:
--   - encoding: n → ∞ with 1 ≤ k ≤ n and 1 ≤ a possibly depending on n, ak/n → 0 → k : ℕ → ℕ and a : ℕ → ℝ with 1 ≤ k n ≤ n and 1 ≤ a n eventually, and a n · k n / n → 0; reason: the paper's asymptotic regime, indexed by n
--   - encoding: = (1 + o(1)) ak/n → ratio / ofReal (a k / n) → 1 in [0, ∞]; reason: the definition of (1 + o(1)); the denominator is eventually positive and finite
--   - reading: the lower bound is achieved asymptotically by a fixed binary randomized-response mechanism → ∃ ε_n → 0 such that eventually, for every integrable product prior, some IsBinaryRR mechanism that is private, non-interactive and respects U_{k,n} has reward ≥ (1 − ε_n)(ak/n) M_k; reason: the mechanism of the proof of Theorem 18 (p.12), whose error depends on n, k, a only
--   - encoding: with an explicit finite-n error bound → stated as Theorem 18, a separate item; reason: the paper proves Theorem 6 through Theorem 18 (§8, p.11)
--   - encoding: inf_X W(X) / M(X) → ratioN / ratioI: the infimum in [0, ∞] over probability priors with finite means and 0 < M < ∞; reason: the priors for which the ratio is defined; on them it is a quotient of finite numbers with positive denominator
--   - encoding: every product prior → every family of probability measures on ℝ≥0 with finite means, indexed by arrival position; reason: the standing assumption of §2: values are independent, non-negative and integrable
--   - encoding: W^I and W^N of Definition 8 → the published WI and WN (suprema in [0, ∞] over output types Z : Type and private mechanisms with behaviour-strategy acceptance kernels); reason: the published base model of this mission, whose conventions are listed with LDPSelect.theorem_1
-- source:
--   Chen, Wang, When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy, STOC 2027 submission (manuscript sha256 2e2d6157…), Theorem 6, p.3 (pdf p.4)

import Mathlib
import Definitions.Def_LDPSelect_Values
import Definitions.Def_LDPSelect_Supplement_Matroid
import Definitions.Def_LDPSelect_Supplement_Ratios
import Definitions.Def_LDPSelect_Supplement_BinaryRR

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LDPSelect.Supplement

open LDPSelect

/-- Chen, Wang, *When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy*, STOC 2027 submission (manuscript sha256 2e2d6157…), Theorem 6, p.3 (pdf p.4).

Let `n → ∞` with `1 ≤ k ≤ n` and `1 ≤ a < ∞` possibly depending on `n`. If `ak/n → 0`, then
`inf_X W^N_k(X) / E[sum of the k largest values] = (1 + o(1)) ak/n`, and the same holds for `W^I_k`. The
lower bound is achieved asymptotically by a fixed binary randomized-response mechanism.

**Formalization Note.** `k` and `a` are functions of `n`, and the hypotheses on them need only hold
eventually. `(1 + o(1)) ak/n` is the statement that the ratio divided by `ak/n` tends to `1`, computed in
`ℝ≥0∞` (the denominator is eventually positive and finite). The last clause gives one error sequence
`ε_n → 0`, uniform in the prior: for every integrable product prior some binary randomized-response
mechanism (`IsBinaryRR`) respecting `U_{k,n}` earns at least `(1 − ε_n)(ak/n) M_k`. The explicit finite-`n`
error bound is Theorem 18, a separate item. -/
theorem theorem_6 (k : ℕ → ℕ) (a : ℕ → ℝ)
    (hk : ∀ᶠ n in atTop, 1 ≤ k n ∧ k n ≤ n) (ha : ∀ᶠ n in atTop, 1 ≤ a n)
    (hlim : Tendsto (fun n : ℕ => a n * k n / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ratioN (a n) (unifFam (k n) n) / ENNReal.ofReal (a n * k n / n))
      atTop (𝓝 1) ∧
    Tendsto (fun n : ℕ => ratioI (a n) (unifFam (k n) n) / ENNReal.ofReal (a n * k n / n))
      atTop (𝓝 1) ∧
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ n in atTop, ∀ P : Fin n → Measure ℝ≥0,
      (∀ i, IsProbabilityMeasure (P i)) → IsIntegrablePrior P →
      ∃ M : Mechanism n Bool, IsBinaryRR (a n) M ∧ M.Private (a n) ∧ M.NonInteractive ∧
        M.Respects (unifFam (k n) n) ∧
        ENNReal.ofReal ((1 - ε n) * (a n * k n / n)) * prophet (unifFam (k n) n) P ≤
          M.reward P := by sorry

end LDPSelect.Supplement
