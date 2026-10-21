-- Prove2me | Theorems.Thm_HochbaumShmoys_Uniform_all_pack_relaxed_decision
-- name    : HochbaumShmoys.Uniform.all_pack_relaxed_decision
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:42:34.732811+00:00
-- url     : https://prove2.me/theorems/531ab322-77b4-4356-8d5d-fc07c5063e5b
-- title:
--   §3, p. 549 — all-pack is a $(2\varepsilon+\varepsilon^2)$-relaxed decision procedure
-- statement:
--   Let $N\ge2$ and $\delta=1/N$, and fix the numbers $m$ of bins and $n$ of pieces. Every resolution $D$ of the procedure all-pack at parameter $\delta$ (any way of making its arbitrary choices) is a $(2\delta+\delta^2)$-relaxed decision procedure: for every instance with piece sizes $p_j>0$ and bin sizes $b_i>0$,
--
--   1. if $D(p,b)$ is a packing $\sigma$, then $\sum_{j\in\sigma^{-1}(i)}p_j\le(1+2\delta+\delta^2)\,b_i$ for every bin $i$;
--   2. if $D(p,b)$ is "none", then there is no truly feasible packing of $p$ into $b$.
--
--   This is the bin-packing procedure that the binary search of §2 calls; together with the size bound of Corollary 2 it gives the polynomial approximation scheme.
--
--   **Formalization Note** all-pack sorts and normalizes the bins itself, so no sortedness hypothesis appears; the instances are unrestricted apart from positivity. $2\delta+\delta^2$ is the paper's $2\varepsilon+\varepsilon^2$ with $\varepsilon=\delta=1/N$.
-- source:
--   Hochbaum & Shmoys, A Polynomial Approximation Scheme for Scheduling on Uniform Processors: Using the Dual Approximation Approach, SIAM J. Comput. 17(3) 1988, p. 549, §3 — all-pack is a (2ε + ε²)-relaxed decision procedure

import Mathlib
import Definitions.Def_HochbaumShmoys_Uniform_Packing
import Definitions.Def_HochbaumShmoys_Uniform_AllPack

namespace HochbaumShmoys.Uniform

theorem all_pack_relaxed_decision (N : ℕ) (hN : 2 ≤ N) (m n : ℕ)
    (D : (Fin n → ℝ) → (Fin m → ℝ) → Option (Fin n → Fin m))
    (hD : IsAllPackResolution N D) :
    IsRelaxedDecisionProcedure (2 * (N : ℝ)⁻¹ + ((N : ℝ)⁻¹) ^ 2) D := by sorry

end HochbaumShmoys.Uniform
