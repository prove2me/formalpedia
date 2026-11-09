-- Prove2me | Theorems.Thm_MildHamilton_Main_lemma_4_5
-- name    : MildHamilton.Main.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:50:57.785419+00:00
-- url     : https://prove2.me/theorems/44c52074-cc42-434d-b3a8-d33be72ab7ed
-- title:
--   Lemma 4.5, pp. 8–9 — comparators from subdivided even cycles
-- statement:
--   For every even $k\ge4$ there exists a graph $G_k$ which is an $A,B$-Hamilton-router, where $A,B\subseteq V(G_k)$ are disjoint with $|A|=|B|=2$, such that:
--
--   1. $\Delta(G_k)\le3$;
--   2. $G_k$ is obtained from a $k$-cycle $C$ by identifying some $A,B\subseteq V(C)$, pairing up the vertices of $V(C)\setminus(A\cup B)$, and, for each pair, adding a path of arbitrary length between its two vertices, the added paths being pairwise vertex-disjoint and each meeting $C$ precisely in its two endpoints.
--
--   The sets $A$, $B$ and the pairing are chosen once, and the conclusion holds for every choice of the path lengths. This is what allows comparators to be built from a short even cycle and connecting paths of uncontrolled length.
--
--   Differences from the source:
--   - reading: a graph G_k with a path of arbitrary length for each pair → ∃ A, B and a pairing P, then for all lengths ≥ 1 a subdivided graph exists, and every such graph is a comparator of maximum degree at most 3; reason: the proof fixes the pairing and states that any subdivision works; this is the strongest reading and the one Lemma 4.7 uses
-- source:
--   Alp Muyesser, STOC 2027 submission #233 (October 2026), Lemma 4.5, pp. 8–9

import Mathlib
import Definitions.Def_MildHamilton_Main_Router

namespace MildHamilton.Main

open Classical in
/-- Lemma 4.5 (Muyesser, STOC 2027 submission #233, pp. 8–9): for even `k ≥ 4` there are disjoint `A`, `B` of
size 2 in the `k`-cycle and a pairing `P` of the remaining vertices such that, for every assignment
of lengths to the pairs, a subdivided graph with those lengths exists, and every graph so obtained is an
`A, B`-comparator of maximum degree at most 3. -/
theorem lemma_4_5 (k : ℕ) [NeZero k] (hk : Even k) (h4 : 4 ≤ k) :
    ∃ (A B : Finset (Fin k)) (P : Finset (Fin k × Fin k)),
      Disjoint A B ∧ A.card = 2 ∧ B.card = 2 ∧ IsCyclePairing A B P ∧
      (∀ L : Fin k × Fin k → ℕ, (∀ e ∈ P, 1 ≤ L e) →
        ∃ (V : Type) (_ : Fintype V) (S : SimpleGraph V) (c : Fin k → V)
          (Q : Fin k × Fin k → List V),
          IsSubdividedCycle P S c Q ∧ ∀ e ∈ P, (Q e).length = L e + 1) ∧
      ∀ (V : Type) [Fintype V] (S : SimpleGraph V) (c : Fin k → V)
        (Q : Fin k × Fin k → List V), IsSubdividedCycle P S c Q →
        IsComparator S.Adj Finset.univ (A.image c) (B.image c) ∧ S.maxDegree ≤ 3 := by sorry

end MildHamilton.Main
