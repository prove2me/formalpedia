-- Prove2me | Theorems.Thm_MultitaskContracts_Supplement_theorem_7
-- name    : MultitaskContracts.Supplement.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:10:26.896196+00:00
-- url     : https://prove2.me/theorems/fcd9d2dd-6985-4fbd-a571-5c5d8e014479
-- title:
--   Theorem 7 — under independence, the price of separation of Min-Budget is $|K|$
-- statement:
--   Let $K$ be a finite nonempty set of tasks. Over all instances on $K$ with independent tasks (heterogeneous costs $c_k>0$ and probabilities $0\le q_k<p_k\le1$), the price of separation of Min-Budget, as defined in Definition 1, is $|K|$:
--   $$\mathrm{PoSep}_{\mathrm{MinBudget}}\;=\;\sup_{I}\frac{\mathrm{OPT}^{\mathrm{Sep}}_{\mathrm{MinBudget}}(I)}{\mathrm{OPT}^{\mathrm{Bun}}_{\mathrm{MinBudget}}(I)}\;=\;|K|.$$
--
--   Bundling reduces the minimum budget needed to implement full effort by at most a factor $|K|$, and this factor is approached. Together with the Min-Pay counterpart (Theorem 2), it shows that the price of separation is $|K|$ for both unbudgeted objectives under independence.
--
--   **Formalization Note** The optima, the ratio and the supremum are in $[0,\infty]$, with the published price of separation ($\infty/\infty:=1$). $K$ is nonempty: for $K=\emptyset$ both optima are $0$ and the ratio is undefined. The supremum is not claimed to be attained.
--
--   Differences from the source:
--   - encoding: |K| for the task set of the instances → [Nonempty K]; reason: for K = ∅ both optima are 0 and Definition 1's ratio 0/0 is undefined; the paper's task sets are nonempty
-- source:
--   Saig, Talgam-Cohen, Tolkowsky, Multitask Contracts: Realizing the Value of Bundling, STOC 2027 submission (held version, sha256 e991a51a…), Theorem 7, p.38 (PDF p.40)

import Mathlib
import Definitions.Def_MultitaskContracts_Instance
import Definitions.Def_MultitaskContracts_bundle
import Definitions.Def_MultitaskContracts_separable
import Definitions.Def_MultitaskContracts_priceOfSeparation
import Definitions.Def_MultitaskContracts_Instance_IsIndependent

set_option autoImplicit false

open scoped ENNReal

namespace MultitaskContracts.Supplement

/-- **Theorem 7** (§5.3, p.38, PDF 40). Under independence, the price of separation of
Min-Budget, as defined in Definition 1, is `|K|`: for every finite nonempty set of tasks `K`,
`sup_I OPT^Sep_MinBudget(I)/OPT^Bun_MinBudget(I) = |K|` over all instances on `K` with independent
tasks (heterogeneous `c_k > 0`, `0 ≤ q_k < p_k ≤ 1`).
E. Saig, I. Talgam-Cohen, Y. Tolkowsky, *Multitask Contracts: Realizing the Value of Bundling*,
STOC 2027 submission (held version, sha256 e991a51a…), Theorem 7, p.38.

**Formalization Note.** `K` is nonempty (for `K = ∅` both optima are `0` and the ratio `0/0`
is undefined). Optima, the ratio and the supremum are in `ℝ≥0∞` (published `priceOfSeparation`,
`∞/∞ := 1`). The supremum is not claimed to be attained. -/
theorem theorem_7 (K : Type*) [Fintype K] [DecidableEq K] [Nonempty K] :
    priceOfSeparation (fun I T => I.optMinBudget T) {I : Instance K | I.IsIndependent} =
      (Fintype.card K : ℝ≥0∞) := by sorry

end MultitaskContracts.Supplement
