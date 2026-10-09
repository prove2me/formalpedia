-- Prove2me | Theorems.Thm_KAdaptability_ObjMILP_theorem_2
-- name    : KAdaptability.ObjMILP.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:01:19.135986+00:00
-- url     : https://prove2.me/theorems/e9020b67-9011-4e83-9845-b851065b73a0
-- title:
--   Theorem 2 — the K-adaptability problem 𝒫𝒪_K is equivalent to the MILP (5)
-- statement:
--   Let the data of the two-stage robust binary program with objective uncertainty satisfy the standing assumptions: $\Xi=\{\xi\in\mathbb R^Q: A\xi\le b\}$ is nonempty and bounded, $\mathcal X\subseteq\mathbb R^N_+$ and $\mathcal Y\subseteq\{0,1\}^M$. Let $K\ge1$ and $\mathcal K=\{1,\dots,K\}$. Then problem $\mathcal{PO}_K$,
--   $$\min_{x\in\mathcal X,\ y^k\in\mathcal Y,\ Tx+Wy^k\le h\ \forall k}\ \max_{\xi\in\Xi}\Big[\xi^\top Cx+\min_{k\in\mathcal K}\xi^\top Qy^k\Big],$$
--   is equivalent to the MILP
--   $$\begin{aligned}\text{minimize}\quad & b^\top\alpha\\ \text{subject to}\quad & x\in\mathcal X,\ y^k\in\mathcal Y,\ k\in\mathcal K,\\ & z^k\in\mathbb R^M_+,\ k\in\mathcal K,\ \alpha\in\mathbb R^R_+,\ \beta\in\mathbb R^K_+,\\ & A^\top\alpha=Cx+\sum_{k\in\mathcal K}Qz^k,\quad e^\top\beta=1,\\ & Tx+Wy^k\le h,\ \ z^k\le y^k,\ \ z^k\le\beta_ke,\ \ z^k\ge(\beta_k-1)e+y^k\quad\forall k\in\mathcal K,\end{aligned}\qquad(5)$$
--   in the following sense:
--   1. a decision $(x,y^1,\dots,y^K)$ is feasible in $\mathcal{PO}_K$ if and only if some $(z,\alpha,\beta)$ completes it to a feasible point of (5);
--   2. for every such feasible decision, the objective value of $\mathcal{PO}_K$ equals the minimum of $b^\top\alpha$ over its completions, and this minimum is attained;
--   3. the optimal values of $\mathcal{PO}_K$ and (5) coincide.
--
--   The theorem turns the K-adaptability problem, a min–max–min problem, into a single mixed-integer linear program whose size is polynomial in the input data, so that it can be handed to off-the-shelf MILP solvers.
--
--   **Formalization Note** Objective and optimal values are extended reals (`EReal`), following the paper's convention that max and min mean sup and inf when not attained; the optimal values in part 3 are infima, which need not be attained when $\mathcal X$ is not closed. The hypothesis $K\ge1$ is the paper's $\mathcal K=\{1,\dots,K\}$.
-- source:
--   Hanasusanto, Kuhn, Wiesemann, K-Adaptability in Two-Stage Robust Binary Programming, preprint, Optimization Online 2014/03/4294 (revision of 2015-03-30), p. 13, Theorem 2 (with problem (PO_K) of Observation 1, p. 11)

import Mathlib
import Definitions.Def_KAdaptability_ObjMILP_Problem
import Definitions.Def_KAdaptability_ObjMILP_POK
import Definitions.Def_KAdaptability_ObjMILP_MILP5

open Matrix

namespace KAdaptability.ObjMILP

/-- Theorem 2, p. 13: problem 𝒫𝒪_K is equivalent to the MILP (5). For `K ≥ 1`:
(i) `(x, y¹, …, y^K)` is feasible in 𝒫𝒪_K iff some `(z, α, β)` completes it to a feasible point
of (5); (ii) for every such feasible decision, the objective of 𝒫𝒪_K equals the minimum of `b⊤α`
over its completions, and this minimum is attained; (iii) the optimal values of 𝒫𝒪_K and (5)
coincide (as infima in `EReal`). -/
theorem theorem_2 {N M L nQ R : ℕ} (P : Problem N M L nQ R) (K : ℕ) (hK : 0 < K) :
    (∀ (x : Fin N → ℝ) (ys : Fin K → Fin M → ℝ),
      P.FeasibleK K x ys ↔
        ∃ (zs : Fin K → Fin M → ℝ) (α : Fin R → ℝ) (β : Fin K → ℝ),
          P.MILPFeasible K x ys zs α β) ∧
    (∀ (x : Fin N → ℝ) (ys : Fin K → Fin M → ℝ), P.FeasibleK K x ys →
      P.objPOK K x ys = P.milpValueAt K x ys ∧
        ∃ (zs : Fin K → Fin M → ℝ) (α : Fin R → ℝ) (β : Fin K → ℝ),
          P.MILPFeasible K x ys zs α β ∧ ((P.b ⬝ᵥ α : ℝ) : EReal) = P.objPOK K x ys) ∧
    P.optPOK K = P.optMILP K := by sorry

end KAdaptability.ObjMILP
