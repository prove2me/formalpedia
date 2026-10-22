-- Prove2me | Theorems.Thm_KellyStochasticNetworks_FlowStability_per_flow_concavity_derivative
-- name    : KellyStochasticNetworks.FlowStability.per_flow_concavity_derivative
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:49:23.364329+00:00
-- url     : https://prove2.me/theorems/782c5468-8beb-4f18-adee-4ebe46991421
-- title:
--   Exercise 8.3 — per-flow concavity and derivative
-- statement:
--   Let $w_r>0$, $n_r\in\mathbb N$, and $\alpha>0$. Let $F_n(x)$ be the per-flow objective in (8.1). On its nonnegative finite-utility domain it is concave, for $0<\alpha<1$, $\alpha=1$, and $\alpha>1$. For every route $r$, at a point where $x_r>0$ if $n_r>0$, its coordinate derivative is
--   $$\frac{\partial F_n}{\partial x_r}(x)=w_rn_rx_r^{-\alpha}.$$
--   Inactive coordinates have derivative zero. This supplies the concavity and differential structure of the allocation rule, including the logarithmic case.
--
--   **Formalization Note** The finite-utility domain excludes active zero rates for $\alpha\ge1$, where the source's extended utility is $-\infty$; for $\alpha<1$ concavity includes the zero boundary. The coordinate derivative is a derivative of a one-variable update, so no positivity condition is needed on other coordinates for that clause. Counts of zero are retained.
-- source:
--   Kelly & Yudovina, Stochastic Networks (2014), supplied Lecture Notes PDF, printed p. 189 (PDF p. 197), Exercise 8.3

import Mathlib
import Definitions.Def_KellyStochasticNetworks_FlowStability_Network

namespace KellyStochasticNetworks.FlowStability

/-- Exercise 8.3: the complete per-flow objective, including inactive coordinates.
Concavity is on its finite-valued domain; the zero boundary at alpha >= 1 has extended
utility minus infinity if any active route receives zero service. -/
theorem per_flow_concavity_derivative {R : ℕ} (w : Fin R → ℝ) (n : State R)
    (alpha : ℝ) (ha : 0 < alpha) (hw : ∀ r, 0 < w r) :
    ConcaveOn ℝ (utilityDomain n alpha) (perFlowUtility w n alpha) ∧
    ∀ (x : Fin R → ℝ) (r : Fin R), (0 < n r → 0 < x r) →
      HasDerivAt (fun t => perFlowUtility w n alpha (Function.update x r t))
        (w r * (n r : ℝ) * x r ^ (-alpha)) (x r) := by sorry

end KellyStochasticNetworks.FlowStability
