-- Prove2me | Theorems.Thm_LeGallBrownianMap_equations_3_4
-- name    : LeGallBrownianMap.equations_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:41:21.978572+00:00
-- url     : https://prove2.me/theorems/3ee8f71e-8dfa-473e-80f6-69d59753ef96
-- title:
--   Eqs. (3) and (4) — distances from $\partial$ and the upper bound on distances in the BDG map
-- statement:
--   Let $p\ge2$, $n\ge1$ and $\theta=(\tau,(\ell_v)_{v\in\tau^\circ})\in\mathbb T^p_n$, with contour sequence $v_0,\dots,v_{pn}$ extended periodically. Let $M$ be the planar map built from $\theta$ by the BDG construction, with vertex set $\tau^\circ\cup\{\partial\}$ and graph distance $d_{gr}$. Then:
--
--   1. for every white vertex $v\in\tau^\circ$,
--   $$
--   d_{gr}(\partial,v)=\ell_v-\min\{\ell_w: w\in\tau^\circ\}+1; \tag{3}
--   $$
--   2. if $v=v_i$ and $v'=v_j$ with $i,j\in\{1,\dots,pn\}$ and $i<j$, then
--   $$
--   d_{gr}(v,v')\le \ell_{v_i}+\ell_{v_j}-2\max\Big(\min_{i\le k\le j}\ell_{v_k},\ \min_{j\le k\le i+pn}\ell_{v_k}\Big)+2. \tag{4}
--   $$
--
--   Identity (3) makes labels the distances to the distinguished vertex; the bound (4) is the discrete analogue of $D\le D^\circ$ and underlies the tightness of rescaled distances.
--
--   **Formalization Note** $d_{gr}$ is the graph distance of `bdgGraph θ` ($\partial$ = `none`), compared in $\mathbb Z$ with the labels.
--
--   Differences from the source:
--   - reading: labeled p-trees of T^p_n coding 2p-angulations with n faces (n ≥ 1 throughout, §2.5) → hypothesis 1 ≤ n; reason: for n = 0 the construction has no edge and no 2p-angulation exists; the paper only uses n ≥ 1
--   - encoding: d_gr in the planar map M built from θ → graph distance of bdgGraph θ, the graph given by the paper's edge rule; reason: graph distances depend only on which vertices are joined, which the edge rule specifies
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, §2.2, p.12, eqs. (3) and (4)

import Mathlib
import Definitions.Def_LeGallBrownianMap_labeledPTrees
import Definitions.Def_LeGallBrownianMap_bdgGraph

namespace LeGallBrownianMap

/-- Le Gall, *Uniqueness and universality of the Brownian map*, arXiv:1105.4842v2, §2.2, p.12,
eqs. (3) and (4): "for every vertex v ∈ τ°, we have d_gr(∂, v) = ℓ_v − min{ℓ_w : w ∈ τ°} + 1. (3)
[…] Suppose that v = v_i and v′ = v_j for some i, j ∈ {1, ..., pn} with i < j. Then,
d_gr(v, v′) ≤ ℓ_{v_i} + ℓ_{v_j} − 2 max( min_{i≤k≤j} ℓ_{v_k}, min_{j≤k≤i+pn} ℓ_{v_k} ) + 2. (4)"

For `p ≥ 2`, `n ≥ 1` and every labeled p-tree `θ = (τ, ℓ) ∈ T^p_n`, in the planar map built from
`θ` by the BDG rule (vertex set `τ° ∪ {∂}`, graph distance `d_gr`):
1. (3) `d_gr(∂, v) = ℓ_v − min ℓ + 1` for every white vertex `v`;
2. (4) for `1 ≤ i < j ≤ pn`, `d_gr(v_i, v_j)` is at most
   `Λ_i + Λ_j − 2 max(min_{i≤k≤j} Λ_k, min_{j≤k≤i+pn} Λ_k) + 2`, with the contour sequence
   extended periodically.

**Formalization Note.** `d_gr` is `SimpleGraph.dist` of `bdgGraph θ` (`none` = `∂`), cast to
`ℤ`; labels along the contour are `labelSeq θ k = ℓ_{v_k}` (indices modulo `pn`). -/
theorem equations_3_4 (p n : ℕ) (hp : 2 ≤ p) (hn : 1 ≤ n)
    (θ : Finset (List ℕ+) × (List ℕ+ → ℤ)) (hθ : θ ∈ labeledPTrees p n) :
    (∀ v ∈ θ.1, Even v.length →
      ((bdgGraph θ).dist none (some v) : ℤ) = θ.2 v - minLabel θ + 1) ∧
    ∀ (i j : ℕ) (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ p * n),
      ((bdgGraph θ).dist (some (contourSeq θ.1 i)) (some (contourSeq θ.1 j)) : ℤ) ≤
        labelSeq θ i + labelSeq θ j -
          2 * max ((Finset.Icc i j).inf' ⟨i, Finset.mem_Icc.mpr ⟨le_rfl, hij.le⟩⟩ (labelSeq θ))
            ((Finset.Icc j (i + p * n)).inf'
              ⟨j, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩ (labelSeq θ)) + 2 := by sorry

end LeGallBrownianMap
