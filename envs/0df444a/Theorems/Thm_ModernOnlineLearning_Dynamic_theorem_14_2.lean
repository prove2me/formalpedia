-- Prove2me | Theorems.Thm_ModernOnlineLearning_Dynamic_theorem_14_2
-- name    : ModernOnlineLearning.Dynamic.theorem_14_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:31:44.886487+00:00
-- url     : https://prove2.me/theorems/04386faf-1e5d-4387-b252-f60d220b5455
-- title:
--   Theorem 14.2, p. 228 — online mirror descent dynamic regret with the terminal Bregman term
-- statement:
--   Let $V\subseteq X$ be a nonempty closed convex feasible set in a finite-dimensional real normed space. Let $\psi$ be closed and $\lambda$-strongly convex on $V\cap\operatorname{int}X$, with $\lambda>0$, and let $x_1,\ldots,x_{T+1}$ be an OMD run with constant learning rate $\eta>0$ entirely in $\operatorname{int}X$. For $T\ge1$, every feasible comparator sequence $u_1,\ldots,u_T$ satisfies
--
--   $$
--   \operatorname{DRegret}_T(u_1,\ldots,u_T)\le
--   \frac{B_\psi(u_T;x_1)+Q\sum_{t=2}^T\lVert u_t-u_{t-1}\rVert}{\eta}
--   +\frac{\eta}{2\lambda}\sum_{t=1}^T\lVert g_t\rVert_*^2
--   -\frac{B_\psi(u_T;x_{T+1})}{\eta},
--   \qquad Q=\max_{1\le t\le T}\lVert\nabla\psi(x_t)-\nabla\psi(x_1)\rVert_*.
--   $$
--
--   The theorem measures the cost of comparator movement while retaining the final Bregman improvement. A constant comparator has zero path length.
--
--   **Formalization Note** The horizon and the two denominators are positive. The model uses real-valued losses on the evaluated domain and relative subgradients on $V$, which are weaker than the book's full-space convention but suffice for the displayed comparison. The OMD run includes the interior condition and all permissible argmin choices.
-- source:
--   Orabona, arXiv:1912.13213v10, Theorem 14.2, p. 228 (PDF p. 240)

import Mathlib
import Definitions.Def_ModernOnlineLearning_Dynamic_Defs

namespace ModernOnlineLearning.Dynamic

/-- Theorem 14.2, p. 228: dynamic regret of OMD, including the terminal
Bregman term. The maximum ranges over the nonempty finite set `1..T`. -/
theorem theorem_14_2
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
    (hu : ∀ t ∈ Finset.Icc 1 T, u t ∈ V) :
    dynamicRegret ℓ x u T ≤
      (BeckTeboulleMD.EMDA.bregman ψ (u T) (x 1) +
        maxGradientShift ψ x T hT * pathLength u T) / η +
      (η / (2 * lam)) * (∑ t ∈ Finset.Icc 1 T, ‖g t‖ ^ 2) -
      BeckTeboulleMD.EMDA.bregman ψ (u T) (x (T + 1)) / η := by sorry

end ModernOnlineLearning.Dynamic
