-- Prove2me | Theorems.Thm_JeroslowMLP_Value_lemma_4_3
-- name    : JeroslowMLP.Value.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T10:02:38.727975+00:00
-- url     : https://prove2.me/theorems/afa70789-ac8b-4f21-9cd6-488ff4a10940
-- title:
--   Lemma 4.3, p. 157 — for bounded S₀, the second-to-last mover's problem is solvable and its solution slice is closed
-- statement:
--   Consider a multi-level program with polyhedral feasible set $S_0=\{x:Ax\ge b\}$, nonempty and bounded. Number the players so that the last two movers control $x^1$ and $x^2$. Then for every $x\in S_0$:
--
--   1. there is $x'\in S_2$ that agrees with $x$ on $x^3,\dots,x^p$ (all variables of the earlier movers);
--   2. the set $\{x'\in S_2:\ x' \text{ agrees with } x \text{ on } x^3,\dots,x^p\}$ is closed.
--
--   Three-level programs can fail to have solutions (the §2 Example); this lemma shows that the first two levels from the bottom always behave well on a bounded polyhedron.
--
--   **Formalization Note** The paper's players 1 and 2 are indices 0 and 1; "the set of all such $x\in S_2$" is read as the slice of $S_2$ over the fixed $x^3,\dots,x^p$.
-- source:
--   Jeroslow, The polynomial hierarchy and a simple model for competitive analysis, Math. Programming 32 (1985), p. 157, Lemma 4.3

import Mathlib
import Definitions.Def_JeroslowMLP_Value_Multilevel

namespace JeroslowMLP.Value

open MultilevelProgram

theorem lemma_4_3 {V : Type} [Fintype V] {m : ℕ} (A : Matrix (Fin m) V ℝ) (b : Fin m → ℝ)
    (G : MultilevelProgram V) (hfeas : G.feasible = polyhedron A b)
    (hne : (polyhedron A b).Nonempty) (hbdd : Bornology.IsBounded (polyhedron A b)) :
    (∀ x ∈ polyhedron A b, ∃ x' ∈ G.solSet 2, G.AgreeAbove 1 x x') ∧
    ∀ x ∈ polyhedron A b, IsClosed {x' | x' ∈ G.solSet 2 ∧ G.AgreeAbove 1 x x'} := by sorry

end JeroslowMLP.Value
