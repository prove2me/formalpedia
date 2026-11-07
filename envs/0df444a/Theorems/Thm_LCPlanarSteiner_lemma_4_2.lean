-- Prove2me | Theorems.Thm_LCPlanarSteiner_lemma_4_2
-- name    : LCPlanarSteiner.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:06:09.061869+00:00
-- url     : https://prove2.me/theorems/b964c21f-6262-4b27-84c7-c7dbddca7ce5
-- title:
--   Lemma 4.2 — cumulative three-layer windows: a planar rooted window of density $\le 3c(F^\star)/r$
-- statement:
--   Let $G$ be a graph with nonnegative costs and lengths, $h > 0$, and $(s_i, t_i)$, $i \in [r]$, $r \ge 1$, nonself pairs with fixed simple witnesses $W_i$ from $s_i$ to $t_i$ of length at most $h$. Let $F^\star = \bigcup_i W_i$ and assume $F^\star$ is planar.
--
--   **Lemma 4.2 (Cumulative three-layer windows).** There are a planar rooted graph $M$ and a nonempty assigned set $I \subseteq [r]$ such that
--   $$
--   \frac{c(M)}{|I|} \le \frac{3\, c(F^\star)}{r} .
--   $$
--   Every assigned witness $W_i$, $i \in I$, is unchanged in $M - \{\rho\}$, which is an original subgraph. A spanning tree of $M$ rooted at $\rho$ has at most three directed pieces of length at most $h$ on each root path. $M$ is obtained from $F^\star$ by contracting a weakly connected vertex set to $\rho$ and deleting vertices and arcs; for the first window, $\rho$ is a new vertex joined by a free zero-length pendant arc.
--
--   The windows reduce the forest problem to rooted graphs whose root paths are short, the input of the separator recursion in Lemma 4.3.
--
--   Differences from the source:
--   - reading: the graph is obtained by connected contractions and deletions; a free pendant root is allowed for the first window → the window contracts one weakly connected vertex set Z (possibly empty) to ρ and deletes vertices and arcs; a free zero-length pendant arc ρ → v₀ occurs only when Z is empty; reason: this is the form of the windows M_j in the proof (p.12); the existence of a window of this form implies the printed existence
--   - encoding: a planar rooted graph M; a spanning tree with at most three directed pieces on each root path; c(M)/|I| ≤ 3c(F⋆)/r → a window record (Z, V, A, pendant) with its underlying simple graph planar; parent arcs with orientations and depths; root paths split into three pieces of equal orientation and length ≤ h; c(M)·r ≤ 3c(F⋆)·|I|; reason: Lean convention, same objects; the division is cleared
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), Lemma 4.2 and its proof, p.12

import Mathlib
import Definitions.Def_LCPlanarSteiner_IsSPath
import Definitions.Def_LCPlanarSteiner_plen
import Definitions.Def_LCPlanarSteiner_pcost
import Definitions.Def_LCPlanarSteiner_underlying
import Definitions.Def_LCPlanarSteiner_Window
import Definitions.Def_LCPlanarSteiner_windowGraph
import Definitions.Def_LCPlanarSteiner_Window_IsTree
import Definitions.Def_LCPlanarSteiner_ThreePieces
import Definitions.Def_RobertsonSeymour1986_GM5_IsPlanar

namespace LCPlanarSteiner

/-- **Lemma 4.2 (Cumulative three-layer windows).**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), Lemma 4.2, p.12: "Let F⋆ be a planar union of fixed strict-h witnesses for r nonself indexed
demands, with h > 0. There is a planar rooted graph M and a nonempty assigned set I such that
c(M)/|I| ≤ 3c(F⋆)/r. Every assigned witness is unchanged in M − {ρ}, which is an original subgraph.
A spanning tree of M has at most three directed pieces of length at most h on each root path. The
graph is obtained by connected contractions and deletions; a free pendant root is allowed for the
first window."

Let `G` be well-formed, `h > 0`, and `r ≥ 1` pairs `(s_i, t_i)` with `s_i ≠ t_i`, each with a fixed
simple path `W_i` from `s_i` to `t_i` of length `≤ h`; let `F⋆` be the union of their arcs and assume
its underlying graph is planar. Then there are a window `M` of `F⋆` (a connected contraction `Z` to
`ρ`, deletions, possibly a free pendant root) whose underlying graph is planar, a nonempty index
set `I ⊆ [r]` with `c(M)/|I| ≤ 3c(F⋆)/r`, such that every `W_i` (`i ∈ I`) has all its arcs in `M` and
all its vertices retained (unchanged in `M − {ρ}`), and a spanning tree of `M` rooted at `ρ` each of
whose root paths consists of at most three directed pieces of length `≤ h`.

**Formalization Note.** The division is cleared: `c(M) · r ≤ 3 c(F⋆) |I|`. The window and its tree
are described in `Window`, `windowGraph` and `Window.IsTree`. -/
theorem lemma_4_2 (G : Net) (hG : G.WF) (h : ℚ) (hh : 0 < h) (dem : List (ℕ × ℕ))
    (hr : dem ≠ []) (hself : ∀ d ∈ dem, d.1 ≠ d.2) (Wt : ℕ → List ℕ)
    (hW : ∀ i < dem.length,
      IsSPath G (dem.getD i (0, 0)).1 (dem.getD i (0, 0)).2 (Wt i) ∧ plen G (Wt i) ≤ h)
    (hpl : RobertsonSeymour1986.GM5.IsPlanar
      (underlying G ((Finset.range dem.length).biUnion fun i => (Wt i).toFinset))) :
    ∃ (M : Window) (I : Finset ℕ) (pa : ℕ → Option ℕ × Bool) (dp : ℕ → ℕ),
      M.Valid G ((Finset.range dem.length).biUnion fun i => (Wt i).toFinset) ∧
      RobertsonSeymour1986.GM5.IsPlanar (windowGraph G M) ∧
      I.Nonempty ∧ (∀ i ∈ I, i < dem.length) ∧
      pcost G M.A * dem.length ≤
        3 * pcost G ((Finset.range dem.length).biUnion fun i => (Wt i).toFinset) * I.card ∧
      (∀ i ∈ I, (∀ e ∈ Wt i, e ∈ M.A) ∧ ∀ u ∈ verts G (dem.getD i (0, 0)).1 (Wt i), u ∈ M.V) ∧
      M.IsTree G pa dp ∧
      ∀ v ∈ M.V, ∀ l, RootPath G M pa v l → ThreePieces G h l := by sorry

end LCPlanarSteiner
