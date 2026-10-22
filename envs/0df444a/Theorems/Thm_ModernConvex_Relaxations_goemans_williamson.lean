-- Prove2me | Theorems.Thm_ModernConvex_Relaxations_goemans_williamson
-- name    : ModernConvex.Relaxations.goemans_williamson
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:33:46.023682+00:00
-- url     : https://prove2.me/theorems/82fce97f-6443-4505-86de-8e1b845c5c83
-- title:
--   Theorem 4.3.1 — Goemans–Williamson: OPT ≤ SDP and OPT ≥ 0.87856…·SDP for MAXCUT
-- statement:
--   Let $a_{ij} = a_{ji} \ge 0$, $i, j = 1, \dots, n$, be the arc weights of an $n$-node graph. Let $\mathrm{OPT}$ be the optimal value of the MAXCUT problem
--   $$(4.3.14)\qquad \max_x\Big\{\tfrac14\sum_{i,j=1}^n a_{ij}(1 - x_ix_j) : x_i^2 = 1,\ i = 1,\dots,n\Big\}$$
--   and $\mathrm{SDP}$ the optimal value of its semidefinite relaxation
--   $$(4.3.15)\qquad \max_X\Big\{\tfrac14\sum_{i,j=1}^n a_{ij}(1 - X_{ij}) : X = X^T \succeq 0,\ X_{ii} = 1,\ i = 1,\dots,n\Big\}.$$
--   Then $1 \ge \mathrm{OPT}/\mathrm{SDP} \ge 0.87856\ldots$ (4.3.16); in product form,
--   $$\mathrm{OPT} \le \mathrm{SDP} \qquad\text{and}\qquad \alpha\cdot\mathrm{SDP} \le \mathrm{OPT},$$
--   where $\alpha = 0.87856\ldots$ is the constant of p. 172, $\alpha = \inf_{-1\le x<1} \frac{2\operatorname{acos}(x)}{\pi(1-x)}$.
--
--   The semidefinite relaxation of MAXCUT, solvable in polynomial time, is never more than a factor $1/0.87856\ldots$ above the maximum cut, which is NP-hard to compute.
--
--   **Formalization Note** The book's ratio $\mathrm{OPT}/\mathrm{SDP}$ is undefined when $\mathrm{SDP} = 0$ (all weights zero); the statement uses the product form, which is equivalent when $\mathrm{SDP} > 0$ and true in the degenerate case. $\alpha$ is the exact infimum (definition `gwConstant`), not a rounded decimal. $\mathrm{OPT}$ and $\mathrm{SDP}$ enter through the predicates "is the optimal value" (least upper bound of the objective over the feasible set); both exist for every instance.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 171, Theorem 4.3.1, (4.3.16) (problems (4.3.14), (4.3.15), p. 170; α = 0.87856…, p. 172)

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations

open Matrix

namespace ModernConvex.Relaxations

/-- Ben-Tal–Nemirovski, Theorem 4.3.1 (Goemans–Williamson), p. 171: for weights
`aᵢⱼ = aⱼᵢ ≥ 0`, the optimal value `OPT` of MAXCUT (4.3.14) and the optimal value `SDP` of its
semidefinite relaxation (4.3.15) satisfy `1 ≥ OPT/SDP ≥ 0.87856…` (4.3.16), stated in product
form `OPT ≤ SDP` and `α · SDP ≤ OPT`, where `α = 0.87856…` is `gwConstant`, the constant of
p. 172. -/
theorem goemans_williamson {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ)
    (ha_symm : ∀ i j, a i j = a j i) (ha_nonneg : ∀ i j, 0 ≤ a i j)
    (OPT SDP : ℝ) (hOPT : IsMaxcutValue a OPT) (hSDP : IsMaxcutSDPValue a SDP) :
    OPT ≤ SDP ∧ gwConstant * SDP ≤ OPT := by sorry

end ModernConvex.Relaxations
