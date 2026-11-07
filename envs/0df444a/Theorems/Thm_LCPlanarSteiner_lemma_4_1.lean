-- Prove2me | Theorems.Thm_LCPlanarSteiner_lemma_4_1
-- name    : LCPlanarSteiner.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:06:30.850614+00:00
-- url     : https://prove2.me/theorems/a9d63dcd-91b5-4954-b7be-f798bdbb7594
-- title:
--   Lemma 4.1 — paired one-path junctions: arm sums $\le (1+\eta)h$, $\sum_z c(H_z) \le D_r(1+2M)c(G^\star) \le 11D_rc(G^\star)/\eta$
-- statement:
--   Let $G$ be a graph with nonnegative costs and lengths, $h > 0$, $G^\star$ a set of arcs, and $P \subseteq G^\star$ a simple directed path of length $L \le h$. Let $(s_i, t_i)$, $i \in [r]$, $r \ge 1$, be pairs with simple witnesses $W_i \subseteq G^\star$ from $s_i$ to $t_i$ of length at most $h$, each meeting $P$. For $0 < \eta \le 1$ put $\delta = \eta h/2$ and $M = \lceil (h + L)/\delta \rceil$.
--
--   **Lemma 4.1 (Paired one-path junctions).** $M \le \lceil 4/\eta \rceil$, and there are junctions $(H_z, v_z, I_z)$ with $v_z \in V(P)$ and nonempty $I_z$ partitioning $[r]$ such that
--   $$
--   \mathrm{dist}_{H_z}(s_i, v_z) + \mathrm{dist}_{H_z}(v_z, t_i) \le (1 + \eta)h \quad (i \in I_z), \tag{8}
--   $$
--   $$
--   \sum_z c(H_z) \le D_r (1 + 2M)\, c(G^\star) \le \frac{11 D_r\, c(G^\star)}{\eta} . \tag{9}
--   $$
--   Planarity is not required.
--
--   The paired allowances keep each pair's two budgets summing to $(1+\eta)h$, and the shared-edge exchange bounds the total junction cost.
--
--   **Formalization Note** $h > 0$ is the standing assumption of §§3–4 (p.5, "Until that case is invoked, h > 0").
--
--   Differences from the source:
--   - reading: construction uses at most 2r rational shortest-path searches → not stated; reason: an existence statement has no construction; the count describes how the junctions are found
--   - encoding: fixed simple strict-h witnesses W_i ⊆ G⋆ met by P; junctions with nonempty I_z partitioning [r] → simple paths W_i inside G⋆ of length ≤ h sharing a vertex with P; a finite list of junctions in which every index lies in exactly one I_z; endpoints are vertices; reason: Lean convention, same instances
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), Lemma 4.1, p.10

import Mathlib
import Definitions.Def_LCPlanarSteiner_IsSPath
import Definitions.Def_LCPlanarSteiner_plen
import Definitions.Def_LCPlanarSteiner_pcost
import Definitions.Def_LCPlanarSteiner_Dlog
import Definitions.Def_LCPlanarSteiner_IsJunctionPartition

namespace LCPlanarSteiner

/-- **Lemma 4.1 (Paired one-path junctions).**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), Lemma 4.1, p.10: "Let P ⊆ G⋆ be a directed simple path of length L ≤ h, met by fixed simple
strict-h witnesses W_i ⊆ G⋆ for r original pairs. For 0 < η ≤ 1, put δ = ηh/2 and
M = ⌈(h + L)/δ⌉ ≤ ⌈4/η⌉. There are junctions (H_z, v_z, I_z), with v_z ∈ V(P) and nonempty I_z
partitioning [r], such that dist_{H_z}(s_i, v_z) + dist_{H_z}(v_z, t_i) ≤ (1 + η)h (i ∈ I_z), (8)
Σ_z c(H_z) ≤ D_r(1 + 2M)c(G⋆) ≤ 11D_r c(G⋆)/η. (9) Construction uses at most 2r rational
shortest-path searches. Planarity is not required."

Let `G` be a well-formed graph, `G⋆` a set of arcs, `h > 0`, `P` a simple directed path from `u₀` to
`u₁` inside `G⋆` with `L = ℓ(P) ≤ h`, and `r ≥ 1` pairs `(s_i, t_i)` (vertices) with simple paths
`W_i` from `s_i` to `t_i` inside `G⋆`, `ℓ(W_i) ≤ h`, each sharing a vertex with `P`. For
`0 < η ≤ 1`, `δ = ηh/2` and `M = ⌈(h + L)/δ⌉`: `M ≤ ⌈4/η⌉`, and there is a partition of `[r]` into
junctions with roots on `P` satisfying (8) and both inequalities of (9).

**Formalization Note.** No planarity hypothesis (the lemma says so). `h > 0` is the standing
assumption of §§3–4 (p.5, "Until that case is invoked, h > 0"). "Met by" is a common vertex. The
number of shortest-path searches describes the construction and is not stated. -/
theorem lemma_4_1 (G : Net) (hG : G.WF) (Gs : Finset ℕ) (h : ℚ) (hh : 0 < h)
    (u₀ u₁ : ℕ) (P : List ℕ) (hP : IsSPath G u₀ u₁ P) (hPG : ∀ e ∈ P, e ∈ Gs)
    (hL : plen G P ≤ h) (dem : List (ℕ × ℕ)) (hr : dem ≠ [])
    (hdem : ∀ d ∈ dem, d.1 < G.n ∧ d.2 < G.n) (W : ℕ → List ℕ)
    (hW : ∀ i < dem.length,
      IsSPath G (dem.getD i (0, 0)).1 (dem.getD i (0, 0)).2 (W i) ∧ (∀ e ∈ W i, e ∈ Gs) ∧
        plen G (W i) ≤ h ∧ ∃ x ∈ verts G (dem.getD i (0, 0)).1 (W i), x ∈ verts G u₀ P)
    (η : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) :
    ⌈(h + plen G P) / (η * h / 2)⌉₊ ≤ ⌈4 / η⌉₊ ∧
    ∃ zs : List (Finset ℕ × ℕ × Finset ℕ),
      (∀ z ∈ zs, z.2.1 ∈ verts G u₀ P) ∧
      IsJunctionPartition G dem zs ((1 + η) * h) ∧
      (zs.map fun z => pcost G z.1).sum ≤
        (Dlog dem.length : ℚ) * (1 + 2 * ⌈(h + plen G P) / (η * h / 2)⌉₊) * pcost G Gs ∧
      (Dlog dem.length : ℚ) * (1 + 2 * ⌈(h + plen G P) / (η * h / 2)⌉₊) * pcost G Gs ≤
        11 * (Dlog dem.length : ℚ) * pcost G Gs / η := by sorry

end LCPlanarSteiner
