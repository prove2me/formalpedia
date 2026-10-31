-- Prove2me | Theorems.Thm_MWMSLagrange_sum_sqrt_bound
-- name    : MWMSLagrange.sum_sqrt_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:03:45.697146+00:00
-- url     : https://prove2.me/theorems/0ea5ea31-dd50-45d0-a1fa-4c91e54f1e3d
-- title:
--   Proof of Theorem 2, p.25: $\sum_j\sqrt{\sum_{i\in\mathcal N_j}\rho_{i,j}^2}\le\sqrt{MN}$ and $\le N$
-- statement:
--   Let $\rho$ be an allocation: $\rho_{i,j}\in[0,1]$, zero off the network, and $\sum_{j\in\mathcal M_i}\rho_{i,j}=1$ for every store $i$. Then
--
--   1. (Cauchy–Schwarz) $\displaystyle\sum_{j=1}^M\sqrt{\sum_{i\in\mathcal N_j}\rho_{i,j}^2}\le\sqrt{M\sum_{j=1}^M\sum_{i\in\mathcal N_j}\rho_{i,j}^2}$;
--   2. $\displaystyle\sqrt{M\sum_{j=1}^M\sum_{i\in\mathcal N_j}\rho_{i,j}^2}\le\sqrt{MN}$;
--   3. (inequality of norms) $\displaystyle\sum_{j=1}^M\sqrt{\sum_{i\in\mathcal N_j}\rho_{i,j}^2}\le N$.
--
--   Together they give $\sum_j\sqrt{\sum_{i\in\mathcal N_j}\rho_{i,j}^2}\le\sqrt{\min\{M,N\}N}$, the source of the factor $\min\{M,N\}$ in Theorem 2.
--
--   Differences from the source:
--   - generalization: the SLaBS allocation ρ*_{i,j}(λ*) → any allocation ρ; reason: the chain uses only ρ_{i,j} ∈ [0, 1] and Σ_{j∈M_i} ρ_{i,j} = 1; at ρ* it is the page's chain
--   - encoding: the chains through √(M Σ_j Σ_{i∈N_j} ρ_{i,j}), Σ_j Σ_{i∈N_j} ρ_{i,j} and Σ_i Σ_{j∈M_i} ρ_{i,j} → the first Cauchy–Schwarz step and the two end points √(MN) and N; reason: each omitted step is ρ_{i,j}² ≤ ρ_{i,j}, a swap of finite sums or Σ_{j∈M_i} ρ_{i,j} = 1, so the conjuncts carry the whole chain
-- source:
--   Miao, Jasin, Chao, Asymptotically Optimal Lagrangian Policies for Multi-Warehouse, Multi-Store Systems with Lost Sales, SSRN 3552995 (manuscript, sha256 1146a7f8…), proof of Theorem 2, p.25, the two displays

import Mathlib
import Definitions.Def_MWMSLagrange_Instance
import Definitions.Def_MWMSLagrange_Instance_Nset
import Definitions.Def_MWMSLagrange_IsAllocation

namespace MWMSLagrange

/-- Miao, Jasin, Chao, SSRN 3552995 (manuscript, sha256 1146a7f8…), proof of Theorem 2, p.25:
for an allocation `ρ` (`ρ_{i,j} ∈ [0, 1]`, `∑_{j∈𝓜_i} ρ_{i,j} = 1`),
1. (Cauchy–Schwarz) `∑_{j=1}^M √(∑_{i∈𝓝_j} ρ_{i,j}²) ≤ √(M ∑_{j=1}^M ∑_{i∈𝓝_j} ρ_{i,j}²)`,
2. `√(M ∑_{j=1}^M ∑_{i∈𝓝_j} ρ_{i,j}²) ≤ √(MN)`, and
3. (inequality of norms) `∑_{j=1}^M √(∑_{i∈𝓝_j} ρ_{i,j}²) ≤ N`. -/
theorem sum_sqrt_bound {M N : ℕ} (I : Instance M N) (ρ : Fin N → Fin M → ℝ)
    (hρ : IsAllocation I ρ) :
    (∑ j, Real.sqrt (∑ i ∈ I.Nset j, ρ i j ^ 2)
        ≤ Real.sqrt (M * ∑ j, ∑ i ∈ I.Nset j, ρ i j ^ 2)) ∧
      Real.sqrt (M * ∑ j, ∑ i ∈ I.Nset j, ρ i j ^ 2) ≤ Real.sqrt (M * N) ∧
      ∑ j, Real.sqrt (∑ i ∈ I.Nset j, ρ i j ^ 2) ≤ N := by sorry

end MWMSLagrange
