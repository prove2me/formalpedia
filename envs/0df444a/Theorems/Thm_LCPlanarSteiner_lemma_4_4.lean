-- Prove2me | Theorems.Thm_LCPlanarSteiner_lemma_4_4
-- name    : LCPlanarSteiner.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:06:42.622658+00:00
-- url     : https://prove2.me/theorems/e9f975b7-17fc-42ea-aa2d-ff953e7818ac
-- title:
--   Lemma 4.4 — width-sensitive junctions: strict arm sums $\le h$ and $\sum_z c(H_z) \le (w+1)D_rc(F^\star)$
-- statement:
--   Let $G$ be a graph with nonnegative costs and lengths, $h > 0$, and $F^\star$ a set of arcs that serves $r \ge 1$ nonself pairs $(s_i, t_i)$ within length $h$ and whose simple underlying undirected graph has treewidth at most $w$.
--
--   **Lemma 4.4 (Width-sensitive junctions).** The indices have a partition into original junctions $(H_z, v_z, I_z)$ with $H_z \subseteq F^\star$ such that
--   $$
--   \mathrm{dist}_{H_z}(s_i, v_z) + \mathrm{dist}_{H_z}(v_z, t_i) \le h \quad (i \in I_z),\qquad \sum_z c(H_z) \le (w + 1) D_r\, c(F^\star) .
--   $$
--   Planarity is not needed.
--
--   These strict junctions seed the density LP in the width-sensitive part of Theorem 1.2.
--
--   **Formalization Note** Treewidth is the published `RobertsonSeymour1986.GM5.TreewidthLE`. $h > 0$ is the standing assumption of §§3–4 (p.5).
--
--   Differences from the source:
--   - encoding: F⋆ serves r ≥ 1 nonself indexed pairs within length h, with underlying treewidth at most w; a partition into junctions inside F⋆ → dist_{F⋆}(s_i, t_i) ≤ h with s_i ≠ t_i; TreewidthLE of the simple underlying graph of F⋆; a finite list of junctions with H_z ⊆ F⋆ in which every index lies in exactly one I_z; endpoints are vertices; reason: Lean convention, same instances
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), Lemma 4.4, p.13

import Mathlib
import Definitions.Def_LCPlanarSteiner_pcost
import Definitions.Def_LCPlanarSteiner_Dlog
import Definitions.Def_LCPlanarSteiner_StrictForest
import Definitions.Def_LCPlanarSteiner_underlying
import Definitions.Def_LCPlanarSteiner_IsJunctionPartition
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE

namespace LCPlanarSteiner

/-- **Lemma 4.4 (Width-sensitive junctions).**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), Lemma 4.4, p.13: "Let F⋆ serve r ≥ 1 nonself indexed pairs within length h, with underlying
treewidth at most w. Its indices have a partition into original junctions (H_z, v_z, I_z) inside F⋆
such that dist_{H_z}(s_i, v_z) + dist_{H_z}(v_z, t_i) ≤ h (i ∈ I_z), Σ_z c(H_z) ≤ (w + 1)D_r c(F⋆).
Planarity is not needed for this structural statement."

Let `G` be well-formed, `h > 0`, and `F⋆` a set of arcs in which each of the `r ≥ 1` pairs
`(s_i, t_i)`, `s_i ≠ t_i`, has a walk of length `≤ h`, and whose underlying simple graph has
treewidth `≤ w`. Then `[r]` is partitioned into junctions `(H_z, v_z, I_z)` with `H_z ⊆ F⋆`, arm
sums `≤ h`, and `Σ_z c(H_z) ≤ (w + 1) D_r c(F⋆)`.

**Formalization Note.** No planarity hypothesis. Treewidth is the published
`RobertsonSeymour1986.GM5.TreewidthLE` of the simple underlying graph of `F⋆`. `h > 0` is the
standing assumption of §§3–4 (p.5). -/
theorem lemma_4_4 (G : Net) (hG : G.WF) (h : ℚ) (hh : 0 < h) (dem : List (ℕ × ℕ))
    (hr : dem ≠ []) (hdem : ∀ d ∈ dem, d.1 < G.n ∧ d.2 < G.n) (hself : ∀ d ∈ dem, d.1 ≠ d.2)
    (Fs : Finset ℕ) (hF : StrictForest G dem h Fs) (w : ℕ)
    (htw : RobertsonSeymour1986.GM5.TreewidthLE (underlying G Fs) w) :
    ∃ zs : List (Finset ℕ × ℕ × Finset ℕ),
      (∀ z ∈ zs, z.1 ⊆ Fs) ∧ IsJunctionPartition G dem zs h ∧
      (zs.map fun z => pcost G z.1).sum ≤ ((w : ℚ) + 1) * (Dlog dem.length : ℚ) * pcost G Fs := by sorry

end LCPlanarSteiner
