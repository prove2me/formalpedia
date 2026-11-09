-- Prove2me | Theorems.Thm_MildHamilton_Main_lemma_4_6
-- name    : MildHamilton.Main.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:46:11.635995+00:00
-- url     : https://prove2.me/theorems/5b2b2eb9-78fd-4481-8e09-8f15c126c4fb
-- title:
--   Lemma 4.6, p. 9 — packing short even cycles
-- statement:
--   Let $G$ be an $n$-vertex graph with $D\le\delta(G)$ and $\Delta(G)\le2D$ for some $D\ge100$. Then $G$ contains at least $n/(100\log n)$ vertex-disjoint even-length cycles, each of length at most $3\log n$.
--
--   These cycles are the bases of the comparators of a Hamilton router. Here $\log$ is the natural logarithm.
--
--   Differences from the source: none.
-- source:
--   Alp Muyesser, STOC 2027 submission #233 (October 2026), Lemma 4.6, p. 9

import Mathlib

namespace MildHamilton.Main

/-- Lemma 4.6 (Muyesser, STOC 2027 submission #233, p. 9): packing short even cycles. `log` is natural;
`t` is the number of cycles and `n` the number of vertices. -/
theorem lemma_4_6 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℝ) (hD : 100 ≤ D) (hmin : D ≤ (G.minDegree : ℝ)) (hmax : (G.maxDegree : ℝ) ≤ 2 * D) :
    ∃ (t : ℕ) (u : Fin t → V) (c : ∀ i, G.Walk (u i) (u i)),
      (Fintype.card V : ℝ) / (100 * Real.log (Fintype.card V)) ≤ (t : ℝ) ∧
      (∀ i, (c i).IsCycle ∧ Even (c i).length ∧
        ((c i).length : ℝ) ≤ 3 * Real.log (Fintype.card V)) ∧
      ∀ i j, i ≠ j → List.Disjoint (c i).support (c j).support := by sorry

end MildHamilton.Main
