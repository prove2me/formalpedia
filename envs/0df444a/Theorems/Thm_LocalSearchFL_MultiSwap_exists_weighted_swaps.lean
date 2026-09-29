-- Prove2me | Theorems.Thm_LocalSearchFL_MultiSwap_exists_weighted_swaps
-- name    : LocalSearchFL.MultiSwap.exists_weighted_swaps
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:40:42.322688+00:00
-- url     : https://prove2.me/theorems/3761816e-d855-48f0-8fa8-685eb6ae7843
-- title:
--   §3.4 — weighted swaps with total weight one per o ∈ O and at most (p+1)/p per s ∈ S
-- statement:
--   Let $S$ and $O$ be two sets of facilities with $|S| = |O|$, let $\sigma_S, \sigma_O$ be client assignments, and let $p \ge 1$ be an integer. Then there is a finite collection $W$ of swaps $\langle A, B\rangle$, with $A \subseteq S$, $B \subseteq O$ and $|A| = |B| \le p$, and a positive real weight $w(A,B)$ on each, such that
--
--   1. for every facility $o \in O$,
--   $$\sum_{\langle A,B\rangle \in W,\ o \in B} w(A,B) = 1;$$
--   2. for every facility $s \in S$,
--   $$\sum_{\langle A,B\rangle \in W,\ s \in A} w(A,B) \le \frac{p+1}{p};$$
--   3. if $\langle A, B\rangle \in W$, then $\mathrm{capture}(A) \subseteq B$;
--   4. the deleted sets $A$ of any two swaps of $W$ are equal or disjoint.
--
--   Each swap in $W$ lies in the $p$-swap neighbourhood, so local optimality gives $\mathrm{cost}((S \setminus A) \cup B) - \mathrm{cost}(S) \ge 0$ for each; the weights are what the analysis uses to add these inequalities up.
--
--   **Formalization Note** The swaps are built in the paper from the partition of Claim 3.1: a block with $|A_i| = |B_i| \le p$ gives the swap $\langle A_i, B_i\rangle$ with weight $1$, and a block with $|A_i| = |B_i| = q > p$ gives the $q(q-1)$ swaps $\langle s, o\rangle$ ($s$ one of $q-1$ good facilities of $A_i$, $o \in B_i$) with weight $1/(q-1)$. Property 4 is not printed as a property but is immediate from that construction (each deleted set is a block $A_i$ or a single facility of a block); it records the structure that the partition of $N_O(o)$ in Property 3.2 relies on. The inequalities from local optimality are not restated here; they follow from the definition of local optimality.
-- source:
--   Arya, Garg, Khandekar, Meyerson, Munagala, Pandit, Local Search Heuristics for k-Median and Facility Location Problems, SIAM J. Comput. 33(3), 2004, pp. 552–553, §3.4, the weighted swaps and their properties 1–3

import Mathlib
import Definitions.Def_LocalSearchFL_MultiSwap_capture

namespace LocalSearchFL.MultiSwap

/-- The weighted swaps of §3.4 (pp. 552–553). If `|S| = |O|` and `p ≥ 1`, there is a finite set
`W` of swaps `⟨A, B⟩` with `A ⊆ S`, `B ⊆ O`, `|A| = |B| ≤ p`, and positive real weights `w`, such
that
1. for every `o ∈ O`, the weights of the swaps `⟨A, B⟩` with `o ∈ B` sum to exactly one;
2. for every `s ∈ S`, the weights of the swaps `⟨A, B⟩` with `s ∈ A` sum to at most `(p + 1)/p`;
3. if `⟨A, B⟩ ∈ W`, then `capture(A) ⊆ B`.
Moreover (from the construction: the sets `A` are blocks `A_i` of the partition of Claim 3.1 or
single facilities of a block) the deleted sets of any two swaps are equal or disjoint. -/
theorem exists_weighted_swaps {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) (S O : Finset Fa) (hcard : S.card = O.card) (p : ℕ) (hp : 1 ≤ p) :
    ∃ (W : Finset (Finset Fa × Finset Fa)) (w : Finset Fa × Finset Fa → ℝ),
      (∀ AB ∈ W, AB.1 ⊆ S ∧ AB.2 ⊆ O ∧ AB.1.card = AB.2.card ∧ AB.1.card ≤ p ∧ 0 < w AB) ∧
      (∀ o ∈ O, ∑ AB ∈ W.filter (fun AB => o ∈ AB.2), w AB = 1) ∧
      (∀ s ∈ S, ∑ AB ∈ W.filter (fun AB => s ∈ AB.1), w AB ≤ ((p : ℝ) + 1) / p) ∧
      (∀ AB ∈ W, capture σS σO O AB.1 ⊆ AB.2) ∧
      (∀ AB ∈ W, ∀ AB' ∈ W, AB.1 = AB'.1 ∨ Disjoint AB.1 AB'.1) := by sorry

end LocalSearchFL.MultiSwap
