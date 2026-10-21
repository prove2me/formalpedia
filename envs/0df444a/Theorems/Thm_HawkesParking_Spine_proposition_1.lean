-- Prove2me | Theorems.Thm_HawkesParking_Spine_proposition_1
-- name    : HawkesParking.Spine.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:27.224561+00:00
-- url     : https://prove2.me/theorems/c8cd4569-5bd9-4b52-8eb1-2cdb840db1d3
-- title:
--   Proposition 1, p. 13 — $\bar{\mathcal P}_k$ is the disjoint union of the Dyck regions $\bar{\mathcal P}_{k,d}$
-- statement:
--   Let $k\ge 1$. The unit polytope $\bar{\mathcal P}_k=\{x\in\mathbb R_+^k: x_i<i\ \forall i,\ x_1<\dots<x_k\}$ is the disjoint union of the Dyck regions $\bar{\mathcal P}_{k,d}=\{x\in\mathbb R_+^k: d_i-1\le x_i<d_i\ \forall i,\ x_1<\dots<x_k\}$ over the $k$-step Dyck paths $d\in\mathsf D_k$ (non-decreasing integer vectors with $1\le d_i\le i$):
--   $$\bar{\mathcal P}_k=\bigsqcup_{d\in\mathsf D_k}\bar{\mathcal P}_{k,d}.$$
--
--   The decomposition reduces uniform sampling on $\bar{\mathcal P}_k$ to choosing a region and sampling inside it.
--
--   **Formalization Note.** The disjoint union $\bigsqcup$ of eq. (9) is stated as two conjuncts: the union equals $\bar{\mathcal P}_k$, and the regions of distinct Dyck paths are pairwise disjoint.
-- source:
--   Daw, Conditional Uniformity and Hawkes Processes, arXiv:2202.05335v2, p. 13, Proposition 1, eqs. (9)–(10)

import Mathlib
import Definitions.Def_HawkesParking_Spine_Model

namespace HawkesParking.Spine
theorem proposition_1 (k : ℕ) (hk : 1 ≤ k) :
    unitPolytope k = (⋃ d ∈ dyckPaths k, dyckRegion k d) ∧
      (dyckPaths k : Set (Fin k → ℕ)).PairwiseDisjoint (dyckRegion k) := by sorry
end HawkesParking.Spine
