-- Prove2me | Theorems.Thm_MinSharing_lemma_2_5
-- name    : MinSharing.lemma_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:25:48.689881+00:00
-- url     : https://prove2.me/theorems/871633ba-bb15-4212-bb39-2cb1cf2efe82
-- title:
--   Lemma 2.5 — an fPO weak Pareto improvement with acyclic consumption graph and at most $n-1$ sharings, in $O(n^2m^2(n+m))$ operations
-- statement:
--   For every allocation $z$ (any $n$, $m$, any real valuation matrix $v$) there is a fractionally Pareto-optimal allocation $z^*$ such that
--
--   1. $z^*$ weakly Pareto dominates $z$: $u_i(z^*_i)\ge u_i(z_i)$ for every agent $i$ (equivalently, $z^*$ either Pareto dominates $z$ or gives every agent the same utility);
--   2. the undirected consumption graph $\mathcal{CG}_{z^*}$ is acyclic;
--   3. $z^*$ has at most $n-1$ sharings, hence at most $n-1$ shared objects.
--
--   Moreover $z^*$ can be constructed in strongly polynomial time: there are a real-RAM program $R$ and a constant $K>0$ such that for all $n,m\ge1$, all $v$ and every allocation $z$, the program started on the memory holding $n,m,v,z$ halts within
--   $$K\cdot n^2m^2(n+m)$$
--   steps and outputs an allocation $z^*$ with all the properties above.
--
--   This is the worst-case bound on sharing: restricting attention to fPO allocations with at most $n-1$ sharings loses no fair allocation, which justifies Step 1 of the algorithm of Theorem 3.6(a) and yields Corollary 2.6.
--
--   Differences from the source:
--   - encoding: (a) z* either Pareto dominates z or gives every agent the same utility as z → ∀ i, u_i(z_i) ≤ u_i(z*_i); reason: the form of Appendix B, p.31 ("z* weakly Pareto dominates z"); the two are equivalent
--   - encoding: CG_{z*} is acyclic → SimpleGraph.IsAcyclic of the bipartite agent–object graph on Fin n ⊕ Fin m; reason: the undirected consumption graph is this bipartite graph
--   - reading: constructed in strongly-polynomial time using O(n²m²(n+m)) operations → number of executed instructions of one program of the published real RAM (SmaleNinth.RAMProgram, unit cost, exact real arithmetic) bounded by K times the expression, with the output correct; reason: the paper counts arithmetic operations and comparisons on real numbers (multiplicative Bellman–Ford, App. A p.31; constant-size LPs, p.14)
--   - encoding: O(n²m²(n+m)) for all n, m → n, m ≥ 1 with R and K chosen before n and m; the existence clause holds for all n, m; reason: the expression is 0 when n or m is 0
--   - encoding: z is an allocation → hypothesis IsFeasible z (z ≥ 0, every column sums to 1); reason: the definition of an allocation on p.7
--   - encoding: agents [n] = {1,…,n}, objects [m] = {1,…,m} → Fin n, Fin m (paper index = Lean index + 1); reason: Lean convention; same instances
-- source:
--   Sandomirskiy, Segal-Halevi, Efficient Fair Division with Minimal Sharing, arXiv:1908.01669v3, Lemma 2.5, p.11; restated with (a) as weak Pareto domination and proved in Appendix B, pp.31–32

import Mathlib
import Definitions.Def_CompetitiveChores_RichFamily_Setting
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_MinSharing_Setting
import Definitions.Def_MinSharing_RAMInterface

set_option autoImplicit false

namespace MinSharing

open CompetitiveChores.RichFamily SmaleNinth

/-- **Lemma 2.5** (Sandomirskiy, Segal-Halevi, arXiv:1908.01669v3, p.11; restated and proved in
Appendix B, pp.31–32). For any allocation `z` there is a fractionally PO allocation `z*` such that
(a) `z*` either Pareto dominates `z` or gives every agent the same utility as `z`;
(b) the undirected consumption graph `CG_{z*}` is acyclic;
(c) `z*` has at most `n − 1` sharings (hence at most `n − 1` shared objects).
The allocation `z*` can be constructed in strongly-polynomial time using `O(n²m²(n+m))`
operations.

**Formalization Note** The statement is the conjunction of the existence claim (every `n`, `m`)
and the construction claim. (a) is `∀ i, uᵢ(zᵢ) ≤ uᵢ(z*ᵢ)`, the form of Appendix B, p.31
("`z*` weakly Pareto dominates `z`"), which is equivalent to the disjunction of p.11.
(b) is `SimpleGraph.IsAcyclic` of the bipartite agent–object graph. The construction is a single
program `R` of the published real RAM with one constant `K > 0`, both chosen before `n` and `m`:
on the input memory `pairMem v z` (holding `n`, `m`, `v`, `z`) it halts within `K·n²·m²·(n+m)`
executed instructions, for all `n, m ≥ 1`, with an output allocation `z*` (read from the output
region `outCell`) satisfying fPO and (a)–(c). "Strongly polynomial" is this bound on the number of
real-arithmetic operations, which does not depend on the magnitudes of the entries. -/
theorem lemma_2_5 :
    (∀ (n m : ℕ) (v z : Fin n → Fin m → ℝ), IsFeasible z →
      ∃ zs : Fin n → Fin m → ℝ, IsParetoOptimal v zs ∧
        (∀ i, utilityProfile v z i ≤ utilityProfile v zs i) ∧
        (consumptionSimpleGraph zs).IsAcyclic ∧
        numSharings zs ≤ n - 1 ∧ numSharedObjects zs ≤ n - 1) ∧
    ∃ R : RAMProgram, ∃ K : ℝ, 0 < K ∧
      ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → ∀ v z : Fin n → Fin m → ℝ, IsFeasible z →
        HaltsWithOutputWithin n m R (pairMem v z) (K * n ^ 2 * m ^ 2 * (n + m)) fun zs =>
          IsParetoOptimal v zs ∧ (∀ i, utilityProfile v z i ≤ utilityProfile v zs i) ∧
          (consumptionSimpleGraph zs).IsAcyclic ∧
          numSharings zs ≤ n - 1 ∧ numSharedObjects zs ≤ n - 1 := by sorry

end MinSharing
