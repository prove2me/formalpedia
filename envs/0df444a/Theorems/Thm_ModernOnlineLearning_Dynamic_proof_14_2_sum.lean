-- Prove2me | Theorems.Thm_ModernOnlineLearning_Dynamic_proof_14_2_sum
-- name    : ModernOnlineLearning.Dynamic.proof_14_2_sum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:31:41.782768+00:00
-- url     : https://prove2.me/theorems/58a4ac25-4b71-43ee-b2ff-eec6e57a8c5f
-- title:
--   Proof of Theorem 14.2, p. 229 — summed OMD comparison before choosing the endpoint
-- statement:
--   Let $T\ge1$ and let $x_1,\ldots,x_{T+1}$ be an online mirror descent run with one positive step size $\eta$, a closed $\lambda$-strongly convex regularizer $\psi$, and subgradients $g_t$. For any feasible comparator sequence $u_1,\ldots,u_{T+1}$, the summed inequality in the proof of Theorem 14.2 is
--
--   $$
--   \operatorname{DRegret}_T(u_1,\ldots,u_T)\le
--   \frac{B_\psi(u_{T+1};x_1)-B_\psi(u_{T+1};x_{T+1})}{\eta}
--   +\frac{\eta}{2\lambda}\sum_{t=1}^T\lVert g_t\rVert_*^2
--   +\frac1\eta\sum_{t=1}^T\langle\nabla\psi(x_{t+1})-\nabla\psi(x_1),u_t-u_{t+1}\rangle.
--   $$
--
--   Keeping $u_{T+1}$ free exposes the comparator-shift term before the final specialization $u_{T+1}=u_T$.
--
--   **Formalization Note** The loss sequence has a relative subgradient at each feasible point, and the run's iterates through $T+1$ lie in $V\cap\operatorname{int}X$. The extra comparator is feasible; no path-length bound has been applied yet.
-- source:
--   Orabona, arXiv:1912.13213v10, proof of Theorem 14.2, display “Putting everything together”, p. 229 (PDF p. 241)

import Mathlib
import Definitions.Def_ModernOnlineLearning_Dynamic_Defs

namespace ModernOnlineLearning.Dynamic

/-- The display beginning “Putting everything together” in the proof of
Theorem 14.2, p. 229, before choosing `u (T+1) = u T`. -/
theorem proof_14_2_sum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X V : Set E) (ψ : E → ℝ) (η : ℝ) (ℓ : ℕ → E → ℝ)
    (x u : ℕ → E) (g : ℕ → E →L[ℝ] ℝ) (T : ℕ) (lam : ℝ)
    (hT : 1 ≤ T) (hη : 0 < η) (hlam : 0 < lam)
    (hVsub : V ⊆ X) (hVne : V.Nonempty) (hVclosed : IsClosed V)
    (hVconv : Convex ℝ V) (hXconv : Convex ℝ X)
    (hψclosed : ClosedRegularizerOn X ψ)
    (hψstrict : StrictConvexOn ℝ X ψ)
    (hψdiff : DifferentiableOn ℝ ψ (interior X))
    (hψstrong : StrongConvexOn (V ∩ interior X) lam ψ)
    (hrun : IsOMDRun X V ψ (fun _ => η) ℓ x g T)
    (hu : ∀ t ∈ Finset.Icc 1 (T + 1), u t ∈ V) :
    dynamicRegret ℓ x u T ≤
      (BeckTeboulleMD.EMDA.bregman ψ (u (T + 1)) (x 1) -
        BeckTeboulleMD.EMDA.bregman ψ (u (T + 1)) (x (T + 1))) / η +
      (η / (2 * lam)) * (∑ t ∈ Finset.Icc 1 T, ‖g t‖ ^ 2) +
      (1 / η) * (∑ t ∈ Finset.Icc 1 T,
        (fderiv ℝ ψ (x (t + 1)) - fderiv ℝ ψ (x 1)) (u t - u (t + 1))) := by sorry

end ModernOnlineLearning.Dynamic
