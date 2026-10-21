-- Prove2me | Theorems.Thm_HryniewiczCriterion_czIndex_ge_three_of_bounded_action_approx
-- name    : HryniewiczCriterion.czIndex_ge_three_of_bounded_action_approx
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-20T16:33:34.997992+00:00
-- url     : https://prove2.me/theorems/b4547f0d-efb7-4f51-b65a-975daa7bc0d4
-- title:
--   Dynamical convexity of a star-shaped level passes to the orbits of bounded action of $C^\infty$-close star-shaped levels
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level whose Hamiltonian flow is dynamically convex (every periodic orbit, prime or multiply covered, has $\mu_{CZ}\ge3$). Let $H_k$ be Hamiltonians with strictly star-shaped levels $H_k^{-1}(1)$ and $H_k\to H$ in $C^\infty_{\mathrm{loc}}$. Then for every action bound $A\in\mathbb{R}$ there is $K$ such that for all $k\ge K$, every periodic orbit $R$ of $X_{H_k}$ on $H_k^{-1}(1)$ with $\mathcal A(R)\le A$ satisfies $\mu_{CZ}(R)\ge3$.
--
--   $H_k\to H$ in $C^\infty_{\mathrm{loc}}$ means: for every $m\in\mathbb{N}$ and every compact $K\subset\mathbb{R}^4$, $D^mH_k\to D^mH$ uniformly on $K$. The action of a periodic orbit $R=(x,T)$ is $\mathcal A(R)=\int_0^T\lambda_0(x(t))[\dot x(t)]\,dt$, with $\lambda_0=\tfrac12\sum(q_i\,dp_i-p_i\,dq_i)$ the Liouville form (`liouvilleForm`). The Conley–Zehnder index $\mu_{CZ}(R)$ is `czIndexOfPath` of the linearized flow on $\xi$ written in the global frame $(Z_1,Z_2)$ (`linearizedXiPath`), with its lower semicontinuous extension to degenerate orbits.
--
--   No non-degeneracy is assumed, either for $H$ or for the $H_k$. The orbits of large action of $H_k$ are not controlled, so the levels $H_k^{-1}(1)$ need not be dynamically convex. This is the form in which dynamical convexity of the limit is used for the approximating contact forms $\lambda_k$ in Section 3 of Hryniewicz (2014).
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014) 791-862, arXiv:1105.2077, Section 3.2, p. 21 (the choice of $k_0$ such that every closed $\lambda_k$-Reeb orbit with $\mu_{CZ}\le2$ has action larger than $C$); Section 2.1 (the Conley-Zehnder index of degenerate orbits).

import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking

open HryniewiczCriterion

theorem HryniewiczCriterion.czIndex_ge_three_of_bounded_action_approx (H : R4 → ℝ) (hS : IsStrictlyStarShapedLevel H) (hdc : IsDynamicallyConvex H)
    (Hs : ℕ → R4 → ℝ) (hSk : ∀ k, IsStrictlyStarShapedLevel (Hs k))
    (hconv : (∀ m : ℕ, ∀ K : Set R4, IsCompact K →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (Hs k)) (iteratedFDeriv ℝ m H) Filter.atTop K)) :
    ∀ A : ℝ, ∃ K : ℕ, ∀ k, K ≤ k → ∀ (R : PeriodicOrbit (Hs k)) (Y : ℝ → (R4 →L[ℝ] R4)),
      IsLinearizedFlow (Hs k) R.x Y → (∫ t in (0 : ℝ)..R.T, liouvilleForm (R.x t) (deriv R.x t)) ≤ A →
      3 ≤ czIndexOfPath (linearizedXiPath (Hs k) R Y) := by sorry
