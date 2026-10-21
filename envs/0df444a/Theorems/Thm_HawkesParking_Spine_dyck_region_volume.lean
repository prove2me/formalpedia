-- Prove2me | Theorems.Thm_HawkesParking_Spine_dyck_region_volume
-- name    : HawkesParking.Spine.dyck_region_volume
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:32.588986+00:00
-- url     : https://prove2.me/theorems/08198da7-9ee5-45a2-8aea-df1f8d554ff2
-- title:
--   Proof of Proposition 2, p. 14 — $\mathrm{vol}(\bar{\mathcal P}_{k,d})=\prod_{i=1}^k 1/\kappa_i(d)!$
-- statement:
--   Let $k\ge 1$, let $d\in\mathsf D_k$ be a $k$-step Dyck path and let $\kappa_i(d)=|\{j: d_j=i\}|$ be the number of coordinates of $d$ equal to $i$. The Lebesgue volume of the Dyck region $\bar{\mathcal P}_{k,d}$ is
--   $$\mathrm{vol}\big(\bar{\mathcal P}_{k,d}\big)=\prod_{i=1}^k\frac{1}{\kappa_i(d)!}.$$
--
--   Coordinates sharing the value $d_j=i$ range over an ordered simplex in $[i-1,i)$, and coordinates with different values are unconstrained relative to each other. The volume is the inverse of the density stated in the proof of Proposition 2 and is computed again in the proof of Proposition 3 (p. 16).
-- source:
--   Daw, Conditional Uniformity and Hawkes Processes, arXiv:2202.05335v2, p. 14, proof of Proposition 2; p. 16, proof of Proposition 3

import Mathlib
import Definitions.Def_HawkesParking_Spine_Model

namespace HawkesParking.Spine
open MeasureTheory
theorem dyck_region_volume (k : ℕ) (hk : 1 ≤ k) (d : Fin k → ℕ) (hd : d ∈ dyckPaths k) :
    volume (dyckRegion k d) = ∏ i ∈ Finset.Icc 1 k, ((kappa d i).factorial : ENNReal)⁻¹ := by sorry
end HawkesParking.Spine
