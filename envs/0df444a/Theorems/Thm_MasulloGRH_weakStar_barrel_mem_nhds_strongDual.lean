-- Prove2me | Theorems.Thm_MasulloGRH_weakStar_barrel_mem_nhds_strongDual
-- name    : MasulloGRH.weakStar_barrel_mem_nhds_strongDual
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-20T23:38:10.420272+00:00
-- url     : https://prove2.me/theorems/4c8d50ac-d0fd-430a-ae80-88e8c4cc87df
-- title:
--   A weak-star closed barrel is a strong-dual neighborhood
-- statement:
--   Let $E$ be a Hausdorff complex locally convex space. Suppose $W$ is a weak-star closed, absolutely convex, absorbing subset of its continuous dual $E'$. Then $$W\in\mathcal N_{\beta(E',E)}(0).$$ Here the strong topology is the topology of uniform convergence on bounded subsets of $E$. This form of the bipolar theorem turns a weak-star closed disk into a neighborhood without any metrizability requirement on $E$.
-- source:
--   H. H. Schaefer and M. P. Wolff, Topological Vector Spaces, 2nd ed., Chapter IV, §1 (bipolar theorem) and §6, proof of (6.5), pp. 152–153. https://doi.org/10.1007/978-1-4612-1468-7

import Definitions.Def_MasulloGRH_LocallyConvex

open Set Filter Topology Bornology

namespace MasulloGRH

theorem weakStar_barrel_mem_nhds_strongDual (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsHLCS E) (W : Set (WeakDual ℂ E))
    (hc : IsClosed W) (hb : Balanced ℂ W) (hv : Convex ℝ W) (ha : Absorbent ℂ W) :
    StrongDual.toWeakDual ⁻¹' W ∈ 𝓝 (0 : StrongDual ℂ E) := by sorry

end MasulloGRH
