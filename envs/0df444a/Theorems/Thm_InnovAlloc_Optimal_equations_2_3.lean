-- Prove2me | Theorems.Thm_InnovAlloc_Optimal_equations_2_3
-- name    : InnovAlloc.Optimal.equations_2_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T02:20:33.336792+00:00
-- url     : https://prove2.me/theorems/255330b4-16cf-4f68-9217-37c6591c22a7
-- title:
--   Equations (2)–(3), p. 9 — single-agent optimal effort and success rate
-- statement:
--   Fix an innovator's share $\gamma\in(0,1)$ and a positive resource allocation $b$. If the other agent receives no resources, the innovator maximizes $\gamma(1-e^{-bx})-x$ over efforts $x\ge0$. The unique maximizing effort is $x^*(b)=0$ for $\gamma b<1$ and $x^*(b)=\log(\gamma b)/b$ for $\gamma b\ge1$. Its success probability is
--
--   $$p(b,x^*(b))=\begin{cases}0,&\gamma b\le1,\\1-1/(\gamma b),&\gamma b>1.\end{cases}$$
--
--   The success probability is nondecreasing as the positive resource allocation grows. This gives the single-agent behavior used in the principal's one-agent investment calculation.
--
--   **Formalization Note** The paper's “increasing” is weak monotonicity here: the success rate stays zero until $\gamma b>1$.
-- source:
--   Gao, Fan, Huang & Chen, “Resource Allocation Among Competing Innovators”, SSRN preprint 3658157 (February 2021), p. 9, eqs. (2)–(3)

import Mathlib
import Definitions.Def_InnovAlloc_Optimal_Model

namespace InnovAlloc.Optimal

/-- Equations (2)–(3), p. 9: the single-agent best response and its success rate. -/
theorem equations_2_3 (γ b : ℝ) (hγ : 0 < γ) (hγ1 : γ < 1) (hb : 0 < b) :
    (∀ x : ℝ, 0 ≤ x →
      ((∀ z : ℝ, 0 ≤ z → γ * succ b z - z ≤ γ * succ b x - x) ↔
        x = effortStar γ b)) ∧
    succ b (effortStar γ b) =
      (if γ * b ≤ 1 then 0 else 1 - 1 / (γ * b)) ∧
    MonotoneOn (fun t : ℝ => succ t (effortStar γ t)) (Set.Ioi 0) := by sorry

end InnovAlloc.Optimal
