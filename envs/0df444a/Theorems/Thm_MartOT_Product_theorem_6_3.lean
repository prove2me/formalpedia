-- Prove2me | Theorems.Thm_MartOT_Product_theorem_6_3
-- name    : MartOT.Product.theorem_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:28.004846+00:00
-- url     : https://prove2.me/theorems/debf2835-ad01-4a58-95b1-961d709da483
-- title:
--   Theorem 6.3, p. 37 — for c = ϕ(x)ψ(y), ψ ≥ 0 strictly convex, ϕ ≥ 0 strictly decreasing, π_lc is the unique optimal martingale plan
-- statement:
--   Let $\mu$ and $\nu$ be finite Borel measures on $\mathbb R$ with finite first moments, in convex order: $\mu\preceq_C\nu$, i.e. $\int\varphi\,d\mu\le\int\varphi\,d\nu$ for every convex $\varphi$. Let $\psi:\mathbb R\to[0,\infty)$ be strictly convex, let $\varphi:\mathbb R\to[0,\infty)$ be strictly decreasing, and consider the cost
--
--   $$c(x,y)=\varphi(x)\,\psi(y)\ \ge 0 .$$
--
--   The martingale transport problem asks to minimize $E_\pi[c]=\int c\,d\pi$ over all martingale transport plans $\pi\in\Pi_M(\mu,\nu)$; write $C_M(\mu,\nu)$ for its value. Assume $C_M(\mu,\nu)<+\infty$.
--
--   **Theorem.** The left-curtain coupling $\pi_{lc}$ of $\mu$ and $\nu$ is an optimal martingale transport plan, and it is the only one:
--
--   $$E_{\pi_{lc}}[c]=\min_{\pi\in\Pi_M(\mu,\nu)}E_\pi[c],\qquad E_\pi[c]=E_{\pi_{lc}}[c],\ \pi\in\Pi_M(\mu,\nu)\ \Longrightarrow\ \pi=\pi_{lc}.$$
--
--   The result identifies a second class of costs, besides $c(x,y)=h(y-x)$ with $h'$ strictly convex (Theorem 6.1), for which the left-curtain coupling solves the martingale transport problem, and here it does so uniquely and without any continuity assumption on $\varphi$.
--
--   **Formalization Note** Two hypotheses are read into the printed statement, both disclosed. (1) "Decreasing" is read as strictly decreasing, the paper's own usage (it writes "nondecreasing" for the weak sense): with $\varphi\equiv1$ every martingale plan has cost $\int\psi\,d\nu$, and for $\mu$ uniform on $\{-1,1\}$, $\nu$ uniform on $\{-2,0,2\}$ there are infinitely many, so uniqueness fails. (2) $C_M(\mu,\nu)<+\infty$ is added; the proof starts from an optimal plan with $\int c\,d\pi<+\infty$, and if every martingale plan has infinite cost every plan is optimal. The left-curtain coupling is named through its defining property `IsLeftCurtain` (Theorem 4.18), the cost is the Setting layer's `EReal`-valued `cost`, and optimality (`IsOptimal`) is minimality among martingale plans; no attainment or semicontinuity is assumed.
-- source:
--   arXiv:1208.1509v2, Theorem 6.3, p. 37

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Product

open MeasureTheory

/-- **Theorem 6.3** (p. 37). Let `ψ` be nonnegative and strictly convex and `ϕ` nonnegative and
(strictly) decreasing, and `c(x, y) = ϕ(x)ψ(y)`. For finite measures `μ ⪯C ν` whose martingale
transport problem has a finite value, the left-curtain coupling `π_lc` is the unique optimal
martingale transport plan. -/
theorem theorem_6_3 (μ ν : Measure ℝ) (hμν : MartOT.Var.ConvexLE μ ν) (ψ ϕ : ℝ → ℝ)
    (hψ0 : ∀ y, 0 ≤ ψ y) (hψ : StrictConvexOn ℝ Set.univ ψ)
    (hϕ0 : ∀ x, 0 ≤ ϕ x) (hϕ : StrictAnti ϕ)
    (hfin : MartOT.Var.CM (fun x y => ϕ x * ψ y) μ ν < ⊤) :
    ∃ π : Measure (ℝ × ℝ), MartOT.Var.IsLeftCurtain μ ν π ∧ MartOT.Var.IsOptimal (fun x y => ϕ x * ψ y) μ ν π ∧
      ∀ π' : Measure (ℝ × ℝ), MartOT.Var.IsOptimal (fun x y => ϕ x * ψ y) μ ν π' → π' = π := by sorry

end MartOT.Product
