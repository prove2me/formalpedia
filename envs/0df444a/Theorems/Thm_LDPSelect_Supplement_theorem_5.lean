-- Prove2me | Theorems.Thm_LDPSelect_Supplement_theorem_5
-- name    : LDPSelect.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:06:05.425459+00:00
-- url     : https://prove2.me/theorems/32bae53c-6584-4fa4-b414-57b9f1bede28
-- title:
--   Theorem 5 — exact single-selection frontier $a/(2a+n-2)$, and $(2+\sum_{i<n}b_i-\min_{i<n}b_i)^{-1}$ with user budgets
-- statement:
--   Let $n\ge2$.
--
--   1. For every $1\le a<\infty$,
--   $$\inf_X\frac{W^{\mathrm N}_1(X)}{\mathbb E\max_i X_i}=\frac{a}{2a+n-2}.$$
--   2. With user-specific budgets $1\le a_i<\infty$ and $b_i=1/a_i$, the tight ratio is
--   $$\inf_X\frac{W^{\mathrm N}_1(X)}{\mathbb E\max_i X_i}=\Big(2+\sum_{i<n}b_i-\min_{i<n}b_i\Big)^{-1},$$
--   where the sum and the minimum run over the first $n-1$ users (the budget of the last user does not affect the value).
--
--   Here $W^{\mathrm N}_1$ is the optimal non-interactive reward for selecting at most one user, and the infimum runs over product priors with integrable values and $0<\mathbb E\max_iX_i<\infty$. This settles the competitive ratio of private single selection left open by Azize, Molina, Richard and Perchet.
--
--   **Formalization Note** The users $1,\dots,n$ are `Fin n` values $0,\dots,n-1$, so "$i<n$" is `i.val + 1 < n`. The minimum is an infimum over this nonempty finite index set.
--
--   Differences from the source:
--   - encoding: a = e^ε ≥ 1 (standing assumption) → a real a with 1 ≤ a as a hypothesis; reason: the standing assumption of §2
--   - encoding: inf_X W(X) / M(X) → ratioN / ratioI: the infimum in [0, ∞] over probability priors with finite means and 0 < M < ∞; reason: the priors for which the ratio is defined; on them it is a quotient of finite numbers with positive denominator
--   - encoding: the users i < n and min_{i<n} b_i → indices i : Fin n with i.val + 1 < n; the minimum as ⨅ over this nonempty finite subtype; reason: 1-based users 1..n−1 are Fin values 0..n−2; n ≥ 2 makes the set nonempty
--   - encoding: user-specific budgets a_i → PrivateHet / WNhet / ratioNhet: the published mechanism model with privacy parameter a i at user i; reason: Theorem 5 and A.4; with constant budgets it is the published WN
--   - reading: the tight ratio is (2 + Σ b_i − min b_i)^{−1} → ratioNhet a (unifFam 1 n) equals it; reason: the sentence continues the quantity inf_X W^N_1(X)/E max_i X_i of the first display; 'tight' is equality of the infimum
--   - encoding: (the budget of the last user does not affect the value) → no separate clause; reason: a consequence of the formula, which does not involve a_n
--   - encoding: every product prior → every family of probability measures on ℝ≥0 with finite means, indexed by arrival position; reason: the standing assumption of §2: values are independent, non-negative and integrable
--   - encoding: W^I and W^N of Definition 8 → the published WI and WN (suprema in [0, ∞] over output types Z : Type and private mechanisms with behaviour-strategy acceptance kernels); reason: the published base model of this mission, whose conventions are listed with LDPSelect.theorem_1
-- source:
--   Chen, Wang, When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy, STOC 2027 submission (manuscript sha256 2e2d6157…), Theorem 5, pp.2–3 (pdf pp.3–4)

import Mathlib
import Definitions.Def_LDPSelect_Supplement_Matroid
import Definitions.Def_LDPSelect_Supplement_Ratios
import Definitions.Def_LDPSelect_Supplement_Hetero

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LDPSelect.Supplement

open LDPSelect

/-- Chen, Wang, *When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy*, STOC 2027 submission (manuscript sha256 2e2d6157…), Theorem 5, pp.2–3 (pdf pp.3–4).

For every `n ≥ 2` and `1 ≤ a < ∞`, `inf_X W^N_1(X) / E max_i X_i = a / (2a + n − 2)`. With user-specific
budgets `1 ≤ a_i < ∞` and `b_i = 1/a_i` (the budget of the last user does not affect the value), the tight
ratio is `(2 + Σ_{i<n} b_i − min_{i<n} b_i)^{−1}`.

**Formalization Note.** Single selection is `unifFam 1 n`, whose prophet value is `E max_i X_i`. The
infimum is `ratioN`/`ratioNhet`: over probability priors with finite means and `0 < E max_i X_i < ∞`.
The paper's users `1, …, n` are `Fin n` values `0, …, n − 1`, so `i < n` (1-based) is `i.val + 1 < n`;
the minimum is an infimum over this nonempty finite index set. Equality of the infimum is both the
lower bound and its tightness. -/
theorem theorem_5 :
    (∀ n : ℕ, 2 ≤ n → ∀ a : ℝ, 1 ≤ a →
      ratioN a (unifFam 1 n) = ENNReal.ofReal (a / (2 * a + n - 2))) ∧
    (∀ n : ℕ, 2 ≤ n → ∀ a : Fin n → ℝ, (∀ i, 1 ≤ a i) →
      ratioNhet a (unifFam 1 n) =
        ENNReal.ofReal (2 + ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val + 1 < n), 1 / a i
          - ⨅ i : {i : Fin n // i.val + 1 < n}, 1 / a i)⁻¹) := by sorry

end LDPSelect.Supplement
