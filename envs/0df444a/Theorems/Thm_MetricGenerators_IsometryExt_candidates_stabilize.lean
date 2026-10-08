-- Prove2me | Theorems.Thm_MetricGenerators_IsometryExt_candidates_stabilize
-- name    : MetricGenerators.IsometryExt.candidates_stabilize
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:48.901286+00:00
-- url     : https://prove2.me/theorems/f9b3d4b4-d7f0-4e5e-9dcb-b4f000d70aa3
-- title:
--   §2, p. 387 — C^(0) ⊇ C^(1) ⊇ ⋯ stabilizes after at most |V(G)| steps
-- statement:
--   Let $H$ and $G$ be finite connected graphs, $T\subseteq V(H)$ and $f:T\to V(G)$, and let $C^{(i)}$, $C^{(i)}_u$ be the candidate procedure. Then the sequences are decreasing,
--   $$C^{(i+1)}\subseteq C^{(i)},\qquad C^{(i+1)}_u\subseteq C^{(i)}_u\quad(i\ge 0,\ u\in V(H)),$$
--   and they stabilize after at most $n:=|V(G)|$ steps: for every $k\ge n$,
--   $$C^{(k)}=C^{(n)}\quad\text{and}\quad C^{(k)}_u=C^{(n)}_u\ \ (u\in V(H)).$$
--
--   This justifies taking $C^*:=C^{(n)}$ as the final output of the procedure.
-- source:
--   Sebő and Tannier, On Metric Generators of Graphs, Math. Oper. Res. 29(2):383–393 (2004), DOI 10.1287/moor.1030.0070, p. 387, §2 (unnumbered, after the recursive definition of C^(i))

import Mathlib
import Definitions.Def_MetricGenerators_IsometryExt_Basic
import Definitions.Def_MetricGenerators_IsometryExt_Representation

namespace MetricGenerators.IsometryExt

/-- Sebő and Tannier, *On Metric Generators of Graphs*, Math. Oper. Res. 29(2):383–393 (2004),
DOI 10.1287/moor.1030.0070, §2, p. 387 (unnumbered): the sequence `C^(0) ⊇ C^(1) ⊇ ⋯` is decreasing (and so is
each sequence `C^(i)_u`), and the procedure is stabilized after at most `n := |V(G)|` steps:
`C^(k) = C^(n)` and `C^(k)_u = C^(n)_u` for every `k ≥ n` and every `u ∈ V(H)`.

Formalization Note: `H` and `G` are finite and connected (standing assumption, p. 383); the
statement holds for every `T` and `f`. -/
theorem candidates_stabilize {VH VG : Type*} [Fintype VH] [Fintype VG]
    (H : SimpleGraph VH) (G : SimpleGraph VG) (hH : H.Connected) (hG : G.Connected)
    (T : Finset VH) (f : ↥T → VG) :
    (∀ i : ℕ, candSet H G T f (i + 1) ⊆ candSet H G T f i ∧
      ∀ u : VH, cand H G T f (i + 1) u ⊆ cand H G T f i u) ∧
    (∀ k : ℕ, Fintype.card VG ≤ k →
      candSet H G T f k = candSet H G T f (Fintype.card VG) ∧
      ∀ u : VH, cand H G T f k u = cand H G T f (Fintype.card VG) u) := by sorry

end MetricGenerators.IsometryExt
