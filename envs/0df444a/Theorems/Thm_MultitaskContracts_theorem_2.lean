-- Prove2me | Theorems.Thm_MultitaskContracts_theorem_2
-- name    : MultitaskContracts.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:34:00.647452+00:00
-- url     : https://prove2.me/theorems/f01da088-7e4c-4e6a-baed-dd37281b1044
-- title:
--   Theorem 2 — under independence, the price of separation of Min-Pay is $|K|$
-- statement:
--   Let $K$ be a finite nonempty set of tasks, and consider all instances on $K$ with independent tasks: arbitrary (heterogeneous) costs $c_k>0$ and success probabilities $0\le q_k<p_k\le1$, with $P_S(Y)=\prod_{k\in Y\cap S}p_k\prod_{k\in Y\setminus S}q_k\prod_{k\in S\setminus Y}(1-p_k)\prod_{k\notin S\cup Y}(1-q_k)$. Then the price of separation of Min-Pay over this class is exactly the number of tasks:
--   $$\mathrm{PoSep}_{\mathrm{MinPay}}(\text{independent instances on }K)=\sup_{I}\frac{\mathrm{OPT}^{\mathrm{Sep}}_{\mathrm{MinPay}}(I)}{\mathrm{OPT}^{\mathrm{Bun}}_{\mathrm{MinPay}}(I)}=|K|.$$
--   That is, $\mathrm{OPT}^{\mathrm{Sep}}_{\mathrm{MinPay}}\le|K|\cdot\mathrm{OPT}^{\mathrm{Bun}}_{\mathrm{MinPay}}$ for every independent instance, and the ratio comes arbitrarily close to $|K|$.
--
--   Bundling the tasks into one contract can thus lower the principal's expected payment by a factor linear in the number of tasks, and never by more.
--
--   **Formalization Note** The supremum is not attained when $|K|\ge2$.
--
--   Differences from the source:
--   - encoding: a finite set of tasks K → K nonempty; reason: for K = ∅ both optima are 0 and Definition 1 leaves the ratio 0/0 undefined (it defines only ∞/∞)
--   - encoding: optima defined by min (∞ if infeasible) and the limit (6), ratio with ∞/∞ := 1, supremum → values, ratio (sepRatio) and supremum in ℝ≥0∞, with Min-Pay the infimum over budgets B ≥ 0; reason: same values; the limit of the antitone function B ↦ OPT_FixedBudget(B) is its infimum
-- source:
--   Saig, Talgam-Cohen, Tolkowsky, Multitask Contracts: Realizing the Value of Bundling, STOC 2027 submission (held version, sha256 e991a51a…), Theorem 2, §4.1.3, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_MultitaskContracts_Instance
import Definitions.Def_MultitaskContracts_bundle
import Definitions.Def_MultitaskContracts_separable
import Definitions.Def_MultitaskContracts_priceOfSeparation
import Definitions.Def_MultitaskContracts_Instance_IsIndependent

set_option autoImplicit false

namespace MultitaskContracts

open scoped ENNReal

/-- **Theorem 2** (§4.1.3, p.15, PDF 17). Under independence, the price of separation of Min-Pay,
as defined in Definition 1, is `|K|`: for every finite nonempty set of tasks `K`,
`sup_I OPT^Sep_MinPay(I)/OPT^Bun_MinPay(I) = |K|`, the supremum over all instances on `K` with
independent tasks (heterogeneous `c_k > 0`, `0 ≤ q_k < p_k ≤ 1`).
E. Saig, I. Talgam-Cohen, Y. Tolkowsky, *Multitask Contracts: Realizing the Value of Bundling*,
STOC 2027 submission (held version, sha256 e991a51a…), Theorem 2, p.15.

**Formalization Note.** `K` is nonempty (for `K = ∅` both optima are `0` and Definition 1's ratio
`0/0` is undefined). Optima, the ratio and the supremum are in `ℝ≥0∞` (Definition 1's `∞/∞ := 1`
via `sepRatio`). The supremum is not attained for `|K| ≥ 2`. -/
theorem theorem_2 (K : Type*) [Fintype K] [DecidableEq K] [Nonempty K] :
    priceOfSeparation (fun I T => I.optMinPay T) {I : Instance K | I.IsIndependent} =
      (Fintype.card K : ℝ≥0∞) := by sorry

end MultitaskContracts
