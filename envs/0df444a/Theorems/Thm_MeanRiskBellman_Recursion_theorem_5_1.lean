-- Prove2me | Theorems.Thm_MeanRiskBellman_Recursion_theorem_5_1
-- name    : MeanRiskBellman.Recursion.theorem_5_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:20:23.92761+00:00
-- url     : https://prove2.me/theorems/e16656d2-82cf-4dd5-82a1-8d02f78cc063
-- title:
--   Theorem 5.1, p. 13 — set-valued Bellman equation: P_t(v_t) = cl{Γ_t(−x) | S_t^⊤ψ_t = v_t, ψ_t ∈ Φ_t, x ∈ P_{t+1}(S_{t+1}^⊤ψ_t)}
-- statement:
--   Consider the multi-period mean-risk portfolio problem under Assumption 2.2: a finite filtered probability space with all nonempty events of positive probability, $d$ assets with adapted discounted prices $S_s$, closed conditionally convex trading constraints $\Phi_s$, and a time consistent dynamic convex risk measure $(\rho_t)$. For $v_t\in L_t$ let $\mathcal P_t(v_t)=\operatorname{cl}\big(\Gamma_t(\Psi_t(v_t))+L_t(\mathbb R^2_+)\big)$ be the upper image of the mean-risk problem $D_t(v_t)$, where $\Gamma_t(X)=(-\mathbb E_t(X_1),\rho_t(X_2))$, and let $\mathcal P_T(v_T)=\{(-v_T,-v_T)\}+L_T(\mathbb R^2_+)$ (5.2).
--
--   **Theorem.** For every $t=0,\dots,T-1$ and every $\mathcal F_t$-measurable $v_t$, the upper images have the recursive form
--   $$\mathcal P_t(v_t)=\operatorname{cl}\left\{\begin{pmatrix}-\mathbb E_t(-x_1)\\ \rho_t(-x_2)\end{pmatrix}\ \middle|\ S_t^\top\psi_t=v_t,\ \psi_t\in\Phi_t,\ \begin{pmatrix}x_1\\x_2\end{pmatrix}\in\mathcal P_{t+1}\big(S_{t+1}^\top\psi_t\big)\right\}.\tag{5.1}$$
--
--   The upper image is the infimum of the vector optimization problem $D_t(v_t)$ in the complete lattice of closed upper sets, so it is the natural value function; (5.1) is a set-valued Bellman principle that computes these value functions backwards in time, one period at a time.
--
--   **Formalization Note.** The right-hand side carries a closure and no ordering cone, as in (5.1). $\mathcal P_t$ for $t<T$ is defined directly from whole feasible strategies, not recursively. Assumption 2.2 item 3 ($\Psi_0(v_0)\ne\emptyset$) is not assumed: the identity holds for empty feasible sets too. Random vectors are functions $\Omega\to\mathbb R\times\mathbb R$ with the pointwise componentwise order, closures are in the product topology, and $\mathbb E_t$ is Mathlib's conditional expectation.
-- source:
--   Kováčová & Rudloff, Time consistency of the mean-risk problem, arXiv:1806.10981v2, p. 13, Theorem 5.1, eq. (5.1), with (5.2) (proof Appendix B.2, pp. 31–32)

import Mathlib
import Definitions.Def_MeanRiskBellman_Recursion_Model

open MeasureTheory Filter Topology
open scoped Pointwise

namespace MeanRiskBellman.Recursion

theorem theorem_5_1 {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] (M : Market Ω)
    (hM : M.Assumptions) (t : ℕ) (ht : t < M.T) (v : Ω → ℝ)
    (hv : StronglyMeasurable[M.ℱ t] v) :
    upperImage M t v =
      closure {y | ∃ θ : Ω → Fin M.d → ℝ, ∃ x : Ω → ℝ × ℝ,
        value M t θ = v ∧ θ ∈ M.Φ t ∧ x ∈ upperImage M (t + 1) (value M (t + 1) θ) ∧
        y = Γ M t (-x)} := by sorry

end MeanRiskBellman.Recursion
