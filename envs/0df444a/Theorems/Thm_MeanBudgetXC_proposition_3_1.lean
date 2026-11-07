-- Prove2me | Theorems.Thm_MeanBudgetXC_proposition_3_1
-- name    : MeanBudgetXC.proposition_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:42:08.228885+00:00
-- url     : https://prove2.me/theorems/e06a1596-4182-4ce7-b9a2-b0fb2713e73f
-- title:
--   Proposition 3.1 — exact local-law interface
-- statement:
--   Let $3\le d\le N$. For a vector $p$ of singleton values and a pair array $q$, write $q(i,T)=\sum_{j\in T}q_{ij}$, $p(S)=\sum_{i\in S}p_i$ and $q(E(S))=\sum_{\{i,j\}\subseteq S}q_{ij}$. Then $(p,q)$ are the singleton and pair coordinates of a consistent system of local laws of context size $d$ and activity two if and only if
--   $$q_{ij}\ge0,\qquad p_i\ge q(i,T)\quad(i\notin T,\ |T|=d-1),\qquad H(S):=1-p(S)+q(E(S))\ge0\quad(|S|=d).$$
--
--   This reduces the exponentially many local laws to explicit linear conditions in $(p,q)$. Every later characterization of the pair body starts from it.
--
--   Differences from the source:
--   - encoding: The vertex set is $[N]$ → it is an arbitrary finite type $V$ with $N=|V|$; reason: every finite type is in bijection with $[N]$, so no instance changes
--   - encoding: laws are given on contexts of size at most $d$ → the family is a function on all finite sets, with values on larger sets unconstrained; reason: the statement is existential in the family and never reads those values
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Proposition 3.1, display (1), p.10

import Mathlib
import Definitions.Def_MeanBudgetXC_IsLocalSystem
import Definitions.Def_MeanBudgetXC_singletonMean
import Definitions.Def_MeanBudgetXC_pairProb
import Definitions.Def_MeanBudgetXC_entry
import Definitions.Def_MeanBudgetXC_edgeMass

namespace MeanBudgetXC

/-- **Proposition 3.1** (Exact local-law interface) (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget
Transition for Local Pair Marginals*, STOC 2027 submission, manuscript sha256 882d9c71…9e76,
Section 3.1, p.10, display (1)). For `3 ≤ d ≤ N`, the singleton and pair coordinates `(p, q)` of
consistent local laws of context size `d` and activity two are exactly those with `q_ij ≥ 0`,
`p_i ≥ q(i, T)` for `i ∉ T`, `|T| = d − 1`, and `H(S) = 1 − p(S) + q(E(S)) ≥ 0` for `|S| = d`.

**Formalization Note** The vertex set is a generic finite type `V` with `N = card V`. -/
theorem proposition_3_1 {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ) (hd3 : 3 ≤ d)
    (hdN : d ≤ Fintype.card V) (p : V → ℝ) (q : Pair V → ℝ) :
    (∃ μ : (S : Finset V) → (S → Bool) → ℝ, IsLocalSystem d 2 μ ∧
        (∀ i, singletonMean μ i = p i) ∧ ∀ e, pairProb μ e = q e) ↔
      ((∀ e, 0 ≤ q e) ∧
        (∀ (i : V) (T : Finset V), i ∉ T → T.card = d - 1 → ∑ j ∈ T, entry q i j ≤ p i) ∧
        ∀ S : Finset V, S.card = d → 0 ≤ 1 - ∑ i ∈ S, p i + edgeMass q S) := by sorry

end MeanBudgetXC
