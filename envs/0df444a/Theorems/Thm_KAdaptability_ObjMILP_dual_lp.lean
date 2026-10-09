-- Prove2me | Theorems.Thm_KAdaptability_ObjMILP_dual_lp
-- name    : KAdaptability.ObjMILP.dual_lp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:02:41.396453+00:00
-- url     : https://prove2.me/theorems/318d9f07-0346-4b5e-9c64-f29645bdbfb1
-- title:
--   Proof of Theorem 2 — strong LP duality: the epigraph LP equals its dual, whose minimum is attained
-- statement:
--   Let the uncertainty set $\Xi=\{\xi\in\mathbb R^Q: A\xi\le b\}$ be nonempty and bounded, let $K\ge1$, and fix any $x\in\mathbb R^N$ and $y^1,\dots,y^K\in\mathbb R^M$. Then the epigraph LP has the same optimal value as its dual:
--   $$\max\Big\{\xi^\top Cx+\tau:\ A\xi\le b,\ \tau\le\xi^\top Qy^k\ \forall k\Big\}=\min\Big\{b^\top\alpha:\ \alpha\in\mathbb R^R_+,\ \beta\in\mathbb R^K_+,\ A^\top\alpha=Cx+\sum_{k\in\mathcal K}\beta_kQy^k,\ e^\top\beta=1\Big\},$$
--   and the minimum on the right is attained: some dual feasible $(\alpha,\beta)$ has $b^\top\alpha$ equal to the optimal value of the epigraph LP.
--
--   This is the step of the proof of Theorem 2 that turns the max–min objective of $\mathcal{PO}_K$ into a minimization, so that it can be merged with the outer minimization over $(x,y^1,\dots,y^K)$. The epigraph LP is feasible because $\Xi$ is nonempty and bounded above because $\Xi$ is bounded and $K\ge1$.
--
--   **Formalization Note** Both optimal values are extended reals (`EReal`); the statement asserts their equality and the existence of a dual feasible point attaining it, which in particular shows that both values are finite.
-- source:
--   Hanasusanto, Kuhn, Wiesemann, K-Adaptability in Two-Stage Robust Binary Programming, preprint, Optimization Online 2014/03/4294 (revision of 2015-03-30), p. ec3 (PDF p. 37), Proof of Theorem 2, dual LP by strong LP duality

import Mathlib
import Definitions.Def_KAdaptability_ObjMILP_Problem
import Definitions.Def_KAdaptability_ObjMILP_EvalLPs

open Matrix

namespace KAdaptability.ObjMILP

/-- Proof of Theorem 2, p. ec3: strong LP duality for the epigraph LP. Since `Ξ` is nonempty and
bounded and `K ≥ 1`, the epigraph LP has the same optimal value as its dual
`min {b⊤α : α ≥ 0, β ≥ 0, A⊤α = Cx + Σ_k β_k Qy^k, e⊤β = 1}`, and the dual minimum is attained. -/
theorem dual_lp {N M L nQ R : ℕ} (P : Problem N M L nQ R) (K : ℕ) (hK : 0 < K)
    (x : Fin N → ℝ) (ys : Fin K → Fin M → ℝ) :
    P.epiValue K x ys = P.dualValue K x ys ∧
      ∃ (α : Fin R → ℝ) (β : Fin K → ℝ), P.DualFeasible K x ys α β ∧
        ((P.b ⬝ᵥ α : ℝ) : EReal) = P.epiValue K x ys := by sorry

end KAdaptability.ObjMILP
