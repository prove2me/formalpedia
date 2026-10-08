-- Prove2me | Theorems.Thm_MartOT_Product_curtain_target_least
-- name    : MartOT.Product.curtain_target_least
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:20.277684+00:00
-- url     : https://prove2.me/theorems/c29c7187-349f-4aec-bd7d-c21b8e02de8c
-- title:
--   Proof of Theorem 4.21, p. 32 — ν^π_s ≤ ν, µ|]−∞,s] ⪯C ν^π_s, hence ν^{π_lc}_s = S^ν(µ|]−∞,s]) ⪯C ν^π_s
-- statement:
--   Let $\mu\preceq_C\nu$ be finite Borel measures on $\mathbb R$ with finite first moments, let $\pi_{lc}$ be the left-curtain coupling of $\mu$ and $\nu$, and let $\pi\in\Pi_M(\mu,\nu)$ be any martingale transport plan. For $s\in\mathbb R$ put
--
--   $$\nu^\pi_s=\mathrm{proj}^y_\#\big(\pi|_{(-\infty,s]\times\mathbb R}\big),$$
--
--   the image of the mass $\mu|_{(-\infty,s]}$ under $\pi$. Then for every $s$:
--
--   1. $\nu^\pi_s\le\nu$;
--   2. $\mu|_{(-\infty,s]}\preceq_C\nu^\pi_s$;
--   3. $\nu^{\pi_{lc}}_s\preceq_C\nu^\pi_s$.
--
--   Since $\nu^{\pi_{lc}}_s=S^\nu(\mu|_{(-\infty,s]})$, item 3 says that the left-curtain coupling sends each left part of $\mu$ to the convex-order-least possible target among all martingale plans. This comparison is what makes $\pi_{lc}$ optimal for every cost of product form $\varphi(x)\psi(y)$ with $\varphi$ decreasing.
--
--   **Formalization Note** $\pi_{lc}$ enters through its defining property `IsLeftCurtain μ ν πlc`; nothing is assumed about its existence.
-- source:
--   arXiv:1208.1509v2, §4.4, proof of Theorem 4.21, p. 32

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Product

open MeasureTheory

/-- Proof of **Theorem 4.21** (p. 32): for every martingale plan `π ∈ Π_M(μ, ν)` and every `s`,
`ν^π_s ≤ ν` and `μ|]−∞,s] ⪯C ν^π_s`, hence `ν^{π_lc}_s = S^ν(μ|]−∞,s]) ⪯C ν^π_s`. -/
theorem curtain_target_least (μ ν : Measure ℝ) (hμν : MartOT.Var.ConvexLE μ ν)
    (πlc π : Measure (ℝ × ℝ)) (hlc : MartOT.Var.IsLeftCurtain μ ν πlc) (hπ : MartOT.Var.IsMartingalePlan μ ν π)
    (s : ℝ) :
    MartOT.Var.targetUpTo π s ≤ ν ∧ MartOT.Var.ConvexLE (μ.restrict (Set.Iic s)) (MartOT.Var.targetUpTo π s) ∧
      MartOT.Var.ConvexLE (MartOT.Var.targetUpTo πlc s) (MartOT.Var.targetUpTo π s) := by sorry

end MartOT.Product
