-- Prove2me | Theorems.Thm_HawkesParking_Spine_proposition_3
-- name    : HawkesParking.Spine.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:27.473004+00:00
-- url     : https://prove2.me/theorems/29e57841-9bbf-469b-b447-1712fc80f9f6
-- title:
--   Proposition 3, p. 15 — $P(\Lambda\in\bar{\mathcal P}_{k,d})=P(\vec\pi=d)=k!/((k+1)^{k-1}\prod_i\kappa_i(d)!)$
-- statement:
--   Let $k\ge 1$ and $d\in\mathsf D_k$. Let $\pi$ be a uniformly random parking function of length $k$ with increasing rearrangement $\vec\pi$, and let $\Lambda$ be uniform on the unit polytope $\bar{\mathcal P}_k$. Then
--   $$P\big(\Lambda\in\bar{\mathcal P}_{k,d}\big)=P(\vec\pi=d)=\frac{k!}{(k+1)^{k-1}\prod_{i=1}^k\kappa_i(d)!},$$
--   where $\kappa_i(d)=|\{j: d_j=i\}|$.
--
--   The identity says that sorting a uniform parking function selects each Dyck region with probability proportional to its volume, which is what makes parking functions the "spine" of the uniform law on $\bar{\mathcal P}_k$.
--
--   **Formalization Note.** The two probabilities are stated separately: the first as the $\mathrm{Uni}(\bar{\mathcal P}_k)$-measure of $\bar{\mathcal P}_{k,d}$ (an extended nonnegative real, written with `ENNReal.ofReal` of the real right-hand side), the second as the real ratio $|\{\pi\in\mathsf{PF}_k:\vec\pi=d\}|/|\mathsf{PF}_k|$. All factorials and powers are cast to $\mathbb R$ before dividing; $k\ge 1$ keeps the exponent $k-1$ meaningful.
-- source:
--   Daw, Conditional Uniformity and Hawkes Processes, arXiv:2202.05335v2, p. 15, Proposition 3, eq. (11)

import Mathlib
import Definitions.Def_HawkesParking_Spine_Model

namespace HawkesParking.Spine
open MeasureTheory
theorem proposition_3 (k : ℕ) (hk : 1 ≤ k) (d : Fin k → ℕ) (hd : d ∈ dyckPaths k) :
    unif (unitPolytope k) (dyckRegion k d) =
        ENNReal.ofReal ((k.factorial : ℝ) /
          (((k : ℝ) + 1) ^ (k - 1) * ∏ i ∈ Finset.Icc 1 k, ((kappa d i).factorial : ℝ))) ∧
      ((((parkingFunctions k).filter fun π => sortNat π = d).card : ℝ) /
          ((parkingFunctions k).card : ℝ) =
        (k.factorial : ℝ) /
          (((k : ℝ) + 1) ^ (k - 1) * ∏ i ∈ Finset.Icc 1 k, ((kappa d i).factorial : ℝ))) := by sorry
end HawkesParking.Spine
