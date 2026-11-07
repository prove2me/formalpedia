-- Prove2me | Theorems.Thm_MeanBudgetXC_lemma_4_1
-- name    : MeanBudgetXC.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:43:22.674189+00:00
-- url     : https://prove2.me/theorems/a42e7202-e464-48a4-af70-5cd55bf6bf61
-- title:
--   Lemma 4.1, Eqs. (11)–(12) — triangle-free zero section
-- statement:
--   Let $3\le d\le N$, let $Q$ be a triangle-free graph with maximum degree $\Delta(Q)\le d-1$ and edge set $E$, and let $a\ge2$.
--
--   1. The face of $P^{(a)}_{N,d}$ on which all nonedge coordinates vanish, projected onto $E$, is
--   $$Z_Q=\{x\ge0:c_S\cdot x\le1\ (|S|=d)\}.$$
--   2. Every local system of activity at most $a$ whose nonedge pair probabilities vanish has total singleton mass at least $2\sum_{e\in E}x_e$, where $x$ is its restriction to $E$.
--   3. Every $x\in Z_Q$ arises from such a system whose total singleton mass is exactly $2\sum_{e\in E}x_e$.
--   4. For every $B\ge0$, imposing the mean budget gives exactly
--   $$Z_{Q,B}=Z_Q\cap\Big\{\sum_{e\in E}x_e\le B/2\Big\}.$$
--
--   The face is the same for every activity $a\ge2$, which is why the exponential lower bound is uniform in $a$.
--
--   Differences from the source:
--   - encoding: The vertex set is $[N]$ → it is an arbitrary finite type $V$ with $N=|V|$; reason: every finite type is in bijection with $[N]$, so no instance changes
--   - encoding: the minimum total singleton mass is $2\sum_e x_e$ → a lower bound for every system together with a system attaining it; reason: this is the meaning of a minimum
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Lemma 4.1, displays (11) and (12), pp.17–18

import Mathlib
import Definitions.Def_MeanBudgetXC_budgetBody
import Definitions.Def_MeanBudgetXC_restrictE
import Definitions.Def_MeanBudgetXC_budgetZeroSection

namespace MeanBudgetXC

/-- **Lemma 4.1** (Triangle-free zero section), displays (11) and (12) (Chao–Gao–Qi–Wang, *A Sharp
Mean-Budget Transition for Local Pair Marginals*, STOC 2027 submission, manuscript sha256
882d9c71…9e76, Section 4.1, pp.17–18). Suppose `3 ≤ d ≤ N`, `Q` is triangle-free and
`Δ(Q) ≤ d − 1`. For every activity `a ≥ 2`:
1. the face `{q ∈ P^{(a)}_{N,d} : q_e = 0 for every nonedge e}` projected onto `E` is
   `Z_Q = {x ≥ 0 : c_S · x ≤ 1 (|S| = d)}` (11);
2. among local laws giving `x`, the minimum total singleton mass is `2 ∑_{e ∈ E} x_e`: every
   such system has `∑_i p_i ≥ 2 ∑_e x_e`, and every `x ∈ Z_Q` arises from a system attaining it;
3. imposing the additional mean budget `B ≥ 0` gives exactly
   `Z_{Q,B} = Z_Q ∩ {∑_{e ∈ E} x_e ≤ B/2}` (12).

**Formalization Note** The vertex set is a generic finite type `V` with `N = card V`; `E` is
`Q.edgeSet` and the projection is `restrictE`. -/
theorem lemma_4_1 {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ) (hd3 : 3 ≤ d)
    (hdN : d ≤ Fintype.card V) (Q : SimpleGraph V) [DecidableRel Q.Adj] (htri : Q.CliqueFree 3)
    (hdeg : Q.maxDegree ≤ d - 1) (a : ℕ) (ha : 2 ≤ a) :
    restrictE Q '' {q | q ∈ pairBody V d a ∧ ∀ e : Pair V, e.1 ∉ Q.edgeSet → q e = 0} =
        zeroSection Q d ∧
      (∀ μ : (S : Finset V) → (S → Bool) → ℝ, IsLocalSystem d a μ →
        (∀ e : Pair V, e.1 ∉ Q.edgeSet → pairProb μ e = 0) →
          2 * ∑ e, restrictE Q (pairProb μ) e ≤ ∑ i, singletonMean μ i) ∧
      (∀ x ∈ zeroSection Q d, ∃ μ : (S : Finset V) → (S → Bool) → ℝ, IsLocalSystem d a μ ∧
        (∀ e : Pair V, e.1 ∉ Q.edgeSet → pairProb μ e = 0) ∧ restrictE Q (pairProb μ) = x ∧
          ∑ i, singletonMean μ i = 2 * ∑ e, x e) ∧
      ∀ B : ℝ, 0 ≤ B →
        restrictE Q '' {q | q ∈ budgetBody V d a B ∧ ∀ e : Pair V, e.1 ∉ Q.edgeSet → q e = 0} =
          budgetZeroSection Q d B := by sorry

end MeanBudgetXC
