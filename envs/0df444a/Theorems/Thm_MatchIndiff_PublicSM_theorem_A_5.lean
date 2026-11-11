-- Prove2me | Theorems.Thm_MatchIndiff_PublicSM_theorem_A_5
-- name    : MatchIndiff.PublicSM.theorem_A_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:25:35.790802+00:00
-- url     : https://prove2.me/theorems/c69566c2-424e-48fb-ae33-9f72b763ccbe
-- title:
--   Theorem A.5 — an ordered increasing forest certifies the absence of improving cycles
-- statement:
--   Let $G$ be a loop-free directed graph on a publicly ordered vertex set of size $N$, with a marked subset of its arcs. Then $G$ has no improving cycle if and only if it admits an ordered increasing forest $F$ such that for every arc $u\to v$:
--
--   1. if $u,v$ are incomparable in $F$, then $u\lhd_F v$;
--   2. if $v$ is a proper descendant of $u$ in $F$, then the arc $u\to v$ is unmarked.
--
--   A forest on $N$ vertices uses $O(N\log(N+1))$ bits: when no improving cycle exists the forest can be chosen with sibling positions in $\{0,\dots,N-1\}$, so it is given by a parent in $\{\text{none}\}\cup\{1..N\}$ and a position for each vertex, one of at most
--   $$\big((N+1)N\big)^N\le 2^{2N\lceil\log_2(N+1)\rceil}$$
--   codes. Its structural constraints are public, and conditions 1–2 for an arc depend only on $F$ and that arc, so they can be checked by the owner of the outgoing arc.
--
--   Differences from the source:
--   - generalization: a forest on N vertices uses O(N log(N + 1)) bits → when no improving cycle exists, a forest with all positions < N exists, and the code space Fin N → Option (Fin N) × Fin N has at most 2^(2N⌈log₂(N+1)⌉) elements; reason: an explicit constant implies the O-bound
--   - reading: its structural constraints are public, and its arc constraints can be checked by the owners of the respective outgoing arcs → conditions (i), (ii) are stated per arc u → v and depend only on F, u, v and the mark of u → v; reason: the sentence describes who can check the conditions; the per-arc form is its formal content
--   - encoding: public strict vertex order, marked arcs → vertices Fin N in index order, relations adj and mk with mk ⊆ adj; a cycle written from its earliest vertex v₀ as v₀ :: rest; reason: Lean convention
-- source:
--   Zhang, Zhao, Xu, Xi, Zhao, Structural Complexity of Matching with Indifferences, STOC 2027 submission (manuscript sha256 22dfb437…), p. 27, Theorem A.5

import Mathlib
import Definitions.Def_MatchIndiff_PublicSM_Forest

namespace MatchIndiff.PublicSM

/-- Theorem A.5 (p. 27): a loop-free directed graph on the publicly ordered vertex set `Fin N`,
with a marked subset of its arcs, has no improving cycle if and only if it admits an ordered
increasing forest `F` such that for every arc `u → v`: (i) if `u, v` are incomparable in `F` then
`u ◁_F v`; (ii) if `v` is a proper descendant of `u` then `u → v` is unmarked. The forest can be
taken with parent in `Fin N ∪ {none}` and sibling positions in `{0, …, N - 1}`, so it is one of at
most `2^{2N⌈log₂(N+1)⌉}` codes. -/
theorem theorem_A_5 {N : ℕ} (adj mk : Fin N → Fin N → Prop) (hloop : ∀ v, ¬ adj v v)
    (hmk : ∀ u v, mk u v → adj u v) :
    ((¬ ∃ (v₀ : Fin N) (rest : List (Fin N)), IsImprovingCycle adj mk v₀ rest) ↔
      ∃ F : OrderedForest N, F.IsIncreasing ∧
        ∀ u v, adj u v → (F.Incomparable u v → F.BranchLt u v) ∧ (F.Anc u v → ¬ mk u v)) ∧
    ((¬ ∃ (v₀ : Fin N) (rest : List (Fin N)), IsImprovingCycle adj mk v₀ rest) →
      ∃ F : OrderedForest N, F.IsIncreasing ∧ (∀ v, F.pos v < N) ∧
        ∀ u v, adj u v → (F.Incomparable u v → F.BranchLt u v) ∧ (F.Anc u v → ¬ mk u v)) ∧
    Fintype.card (Fin N → Option (Fin N) × Fin N) ≤ 2 ^ (2 * N * Nat.clog 2 (N + 1)) := by sorry

end MatchIndiff.PublicSM
