-- Prove2me | Theorems.Thm_MultitaskContracts_Supplement_theorem_8
-- name    : MultitaskContracts.Supplement.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:10:59.233186+00:00
-- url     : https://prove2.me/theorems/85a793e6-1844-402c-9e33-a7c32d2e486c
-- title:
--   Theorem 8 — $\mathrm{OPT}^{\mathrm{Bun}}_{\mathrm{MaxUtil}}\le2\,\mathrm{OPT}^{\mathrm{Sep}}_{\mathrm{MaxUtil}}$ under any dependence structure, and $2$ is tight
-- statement:
--   Under any dependence structure, the best separable contract is a $\tfrac12$-approximation of the optimal bundle contract for the principal's utility, and the factor $2$ is tight:
--   1. for every finite task set $K$, every instance $I$ on $K$ (no independence or other dependence assumption) and all rewards $r_k\ge0$,
--   $$\mathrm{OPT}^{\mathrm{Bun}}_{\mathrm{MaxUtil}}\;\le\;2\,\mathrm{OPT}^{\mathrm{Sep}}_{\mathrm{MaxUtil}};$$
--   2. for every $\alpha<2$ there are an instance on finitely many tasks and rewards $r_k\ge0$ with $\mathrm{OPT}^{\mathrm{Bun}}_{\mathrm{MaxUtil}}>\alpha\,\mathrm{OPT}^{\mathrm{Sep}}_{\mathrm{MaxUtil}}$.
--
--   Here $\mathrm{OPT}^{\mathcal T}_{\mathrm{MaxUtil}}$ is the principal's best utility (expected reward minus expected payment, ties in the agent's best response broken in her favour) over the class $\mathcal T$. For Min-Pay, by contrast, no finite approximation factor is achievable with polynomially many value queries beyond independence.
--
--   **Formalization Note** The optima are suprema in the extended reals. In part 2 the finite task set is $\{0,\dots,n-1\}$ for some $n$, since every finite set is in bijection with one.
--
--   Differences from the source:
--   - encoding: the factor 2 is tight → ∀ α < 2, ∃ n, I : Instance (Fin n), r ≥ 0 with (α : EReal) * OPT^Sep_MaxUtil < OPT^Bun_MaxUtil; reason: tightness of a factor means that no smaller factor holds for all instances; every finite task set is equivalent to some Fin n
--   - encoding: OPT^T_MaxUtil := max_{t∈T} u_P(t) → supremum in EReal of the real utilities; reason: equals the maximum wherever it is attained and avoids a junk real sSup
-- source:
--   Saig, Talgam-Cohen, Tolkowsky, Multitask Contracts: Realizing the Value of Bundling, STOC 2027 submission (held version, sha256 e991a51a…), Theorem 8, p.53 (PDF p.55)

import Mathlib
import Definitions.Def_MultitaskContracts_Instance
import Definitions.Def_MultitaskContracts_bundle
import Definitions.Def_MultitaskContracts_separable
import Definitions.Def_MultitaskContracts_Supplement_optMaxUtil

set_option autoImplicit false

open scoped ENNReal

namespace MultitaskContracts.Supplement

/-- **Theorem 8** (App. A.2, p.53, PDF 55). Under any dependence structure, the best separable
contract is a `1/2`-approximation of the optimal bundle contract,
`OPT^Bun_MaxUtil ≤ 2·OPT^Sep_MaxUtil`, and the factor `2` is tight:
(1) for every finite `K`, every instance on `K` and all rewards `r_k ≥ 0`,
`OPT^Bun_MaxUtil ≤ 2·OPT^Sep_MaxUtil`; (2) for every `α < 2` some instance (on finitely many
tasks) with rewards `r_k ≥ 0` has `OPT^Bun_MaxUtil > α·OPT^Sep_MaxUtil`.
E. Saig, I. Talgam-Cohen, Y. Tolkowsky, *Multitask Contracts: Realizing the Value of Bundling*,
STOC 2027 submission (held version, sha256 e991a51a…), Theorem 8, p.53.

**Formalization Note.** `OPT_MaxUtil` is `optMaxUtil` (App. A.1: supremum in `EReal` of the
principal's utility, ties in the best response broken in her favour). No dependence predicate is
assumed in (1). In (2) the finite task set is `Fin n` (every finite set is equivalent to one). -/
theorem theorem_8 :
    (∀ (K : Type*) [Fintype K] [DecidableEq K] (I : Instance K) (r : K → ℝ), (∀ k, 0 ≤ r k) →
      optMaxUtil I r (bundle K) ≤ 2 * optMaxUtil I r (separable K)) ∧
    (∀ α : ℝ, α < 2 → ∃ (n : ℕ) (I : Instance (Fin n)) (r : Fin n → ℝ), (∀ k, 0 ≤ r k) ∧
      (α : EReal) * optMaxUtil I r (separable (Fin n)) < optMaxUtil I r (bundle (Fin n))) := by sorry

end MultitaskContracts.Supplement
