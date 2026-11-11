-- Prove2me | Theorems.Thm_MinKCutII_Main_lemma_4
-- name    : MinKCutII.Main.lemma_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:39:59.149378+00:00
-- url     : https://prove2.me/theorems/40902827-af6a-4c8d-b394-e3f17f7d15a3
-- title:
--   Lemma 4 — two crossing cuts of value at most 2U/k give a k-cut of value at most U (k = 3, 4)
-- statement:
--   Let $G=(V,E,c)$ be a connected multigraph with positive capacities and $n=|V|\ge3$ (the standing assumption of §3), let $k\in\{3,4\}$ and $U>0$. Let $A,S$ be crossing cuts, i.e. the four regions $A\cap S$, $A\setminus S$, $S\setminus A$, $V\setminus(A\cup S)$ are nonempty, with
--   $$c_G(A)\le\frac{2U}{k},\qquad c_G(S)\le\frac{2U}{k}.$$
--   Then there is a $k$-cut of $G$ of value at most $U$ whose parts are unions of the four regions.
--
--   This is the crossing certificate used for $k=3$ in the 3-cut algorithm and for $k=4$ on overflow in the reduction (Algorithm 5).
--
--   Differences from the source:
--
--   - reading: A, S ⊊ V crossing cuts → cuts whose four Venn regions are all nonempty (CutsCross); reason: the proof uses that all four regions are nonempty; under p. 6's set-crossing definition (not disjoint, not nested) the region V \ (A ∪ S) may be empty and the statement fails (INSIGHTS I3)
--   - reading: one can construct from A and S a k-cut of value at most U → there is a k-cut of value at most U whose labelling is constant on the four regions; reason: the construction in the proof uses only unions of the regions
--   - generalization: positive integer capacities → positive real capacities; reason: the statement holds verbatim for real capacities; integers are a special case
--   - encoding: a k-cut → a surjective labelling V → Fin k; reason: a partition into exactly k nonempty labelled parts
-- source:
--   Vaughn, Faster Minimum k-Cut II: Improved Randomized and Deterministic Algorithms for Weighted Graphs, arXiv:2609.27797 (version of November 1, 2026, sha256 b01b5a6f…), p. 8, Lemma 4

import Mathlib
import Definitions.Def_MinKCutII_Main_KCut
import Definitions.Def_MinKCutII_Main_Cuts

set_option autoImplicit false

open CombOpt.MinCut

namespace MinKCutII.Main

/-- **Lemma 4** (p. 8). In a connected graph with positive capacities and `n ≥ 3` vertices (§3), let
`k ∈ {3, 4}`, `U > 0`, and let `A, S` be crossing cuts with `c_G(A), c_G(S) ≤ 2U/k`. Then there is a
k-cut of value at most `U` whose parts are unions of the four regions `A ∩ S`, `A \ S`, `S \ A`,
`V \ (A ∪ S)` (it is constructed from `A` and `S`). -/
theorem lemma_4 {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] (G : CapGraph V E)
    (k : ℕ) (U : ℝ) (A S : Finset V) (hpos : PosCap G) (hconn : IsConnected G)
    (hn : 3 ≤ Fintype.card V) (hk : k = 3 ∨ k = 4) (hU : 0 < U) (hcross : CutsCross A S)
    (hA : IsULight G k U A) (hS : IsULight G k U S) :
    ∃ f : V → Fin k, Function.Surjective f ∧ partVal G f ≤ U ∧
      ∀ x y : V, (x ∈ A ↔ y ∈ A) → (x ∈ S ↔ y ∈ S) → f x = f y := by sorry

end MinKCutII.Main
