-- Prove2me | Theorems.Thm_LogRegretOCO_ONS_regret_le_potential
-- name    : LogRegretOCO.ONS.regret_le_potential
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:36:22.849613+00:00
-- url     : https://prove2.me/theorems/9d1e8a7f-6305-464b-8366-b0116c6f67d0
-- title:
--   §3.2, p. 178 — the regret of ONS is bounded by the potential (1/2β) Σ ∇ₜᵀAₜ⁻¹∇ₜ plus 1/(2β)
-- statement:
--   Let $\mathcal P\subseteq\mathbb R^n$ be nonempty, closed, bounded and convex with $\|x-y\|\le D$ for all $x,y\in\mathcal P$. Let $f_1,f_2,\dots:\mathbb R^n\to\mathbb R$ be differentiable at every point of $\mathcal P$, with $\|\nabla f_t(x)\|\le G$ on $\mathcal P$, and $\alpha$-exp-concave on $\mathcal P$ (that is, $x\mapsto\exp(-\alpha f_t(x))$ is concave on $\mathcal P$), where $G,D,\alpha>0$. Let $x_1,x_2,\dots$ be a run of the Online Newton Step with $\beta=\tfrac12\min\{1/(4GD),\alpha\}$, $\varepsilon=1/(\beta^2D^2)$, $\nabla_t=\nabla f_t(x_t)$ and $A_t=\sum_{i=1}^t\nabla_i\nabla_i^\top+\varepsilon I_n$. Then for every horizon $T$ and every comparator $u\in\mathcal P$,
--   $$
--   \sum_{t=1}^{T}\big(f_t(x_t)-f_t(u)\big)\ \le\ \frac1{2\beta}\sum_{t=1}^{T}\nabla_t^\top A_t^{-1}\nabla_t+\frac1{2\beta}.
--   $$
--
--   This reduces the regret of ONS to the potential $\sum_t\nabla_t^\top A_t^{-1}\nabla_t$, which the linear-algebra lemmas of Appendix 2 bound by $n\log(G^2T/\varepsilon+1)$.
--
--   **Formalization Note** The paper's regret is measured against $\min_{x\in\mathcal P}\sum_t f_t(x)$; the statement is given against every $u\in\mathcal P$, which is equivalent and avoids a real infimum. The result holds for every $T\ge0$ (for $T=0$ both sums are empty). $G,D,\alpha>0$ is the non-degeneracy that the formulas for $\beta$ and $\varepsilon$ presuppose.
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Mach Learn 69 (2007), p. 178, §3.2, proof of Theorem 2, display for Regret_T(ONS)

import Mathlib
import Definitions.Def_LogRegretOCO_ONS_Basic
import Definitions.Def_LogRegretOCO_ONS_Run

namespace LogRegretOCO.ONS

/-- §3.2, display on p. 178 (Hazan–Agarwal–Kale 2007): the regret of an Online Newton Step run is
at most `(1/(2β)) Σ_{t=1}^T ∇_tᵀ A_t⁻¹ ∇_t + 1/(2β)`, against every comparator `u ∈ P`. -/
theorem regret_le_potential {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n)))
    (hP_ne : P.Nonempty) (hP_closed : IsClosed P) (hP_bdd : Bornology.IsBounded P)
    (hP_conv : Convex ℝ P)
    (G D α : ℝ) (hG : 0 < G) (hD : 0 < D) (hα : 0 < α)
    (hdiam : ∀ x ∈ P, ∀ y ∈ P, ‖x - y‖ ≤ D)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hdiff : ∀ t, ∀ x ∈ P, DifferentiableAt ℝ (f t) x)
    (hgrad : ∀ t, ∀ x ∈ P, ‖gradient (f t) x‖ ≤ G)
    (hexp : ∀ t, ConcaveOn ℝ P (fun x => Real.exp (-α * f t x)))
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsONSRun P G D α f x) (T : ℕ) :
    ∀ u ∈ P, ∑ t ∈ Finset.Icc 1 T, (f t (x t) - f t u) ≤
      1 / (2 * onsBeta G D α) *
          ∑ t ∈ Finset.Icc 1 T, quadForm (onsMatrix G D α f x t)⁻¹ (gradient (f t) (x t)) +
        1 / (2 * onsBeta G D α) := by sorry

end LogRegretOCO.ONS
