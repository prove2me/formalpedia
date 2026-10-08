-- Prove2me | Theorems.Thm_GraphonMF_Stability_proposition_2_1
-- name    : GraphonMF.Stability.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:28:51.790396+00:00
-- url     : https://prove2.me/theorems/e78a3b0f-4f9a-4f0b-8490-31be06011af1
-- title:
--   Proposition 2.1 — well-posedness and uniform path moments
-- statement:
--   Under Condition 2.1, the graphon particle system (2.1) has a pathwise solution, and two such solutions driven by the same initial states and Brownian motions have almost surely identical paths for every label $u\in I$. For the same $\varepsilon>0$ as in Condition 2.1, every solution satisfies
--
--   $$\sup_{u\in I}\mathbb E\|X_u\|_{*,T}^{2+\varepsilon}<\infty,$$
--
--   and the family $u\mapsto\mathcal L(X_u)$ is measurable as a map into probability laws on $\mathcal C_d$.
--
--   This establishes existence, uniqueness, moment control, and measurability of the law family used in the stability theorem.
--
--   **Formalization Note** Uniqueness is indistinguishability of continuous paths within the solution class $\mathcal M$. Membership in $\mathcal M$, including measurability, is part of the solution predicate, so the existence clause supplies the final assertion.
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), p. 3591, Proposition 2.1

import Mathlib
import Definitions.Def_GraphonMF_Stability_Setting

open MeasureTheory
open scoped ENNReal NNReal

namespace GraphonMF.Stability

/-- Proposition 2.1, p. 3591: well-posedness and uniform path moments. -/
theorem proposition_2_1 {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (T : ℝ≥0)
    (hT : 0 < T) (P : Measure Ω) (μ0 : I → Measure (State d))
    (X0 : I → Ω → State d) (B : I → ℝ≥0 → Ω → State d)
    (noise : NoiseSetting P μ0 X0 B)
    (b : State d → State d → State d)
    (σ : State d → State d → Matrix (Fin d) (Fin d) ℝ)
    (ε : ℝ) (hc : Cond21 ε μ0 b σ)
    (G : I → I → ℝ) (hG : IsGraphon G) :
    (∃ X : I → Ω → Cd T d, IsGraphonSolution P μ0 X0 B noise G b σ X) ∧
    (∀ X X' : I → Ω → Cd T d,
      IsGraphonSolution P μ0 X0 B noise G b σ X →
      IsGraphonSolution P μ0 X0 B noise G b σ X' →
      ∀ u, ∀ᵐ ω ∂P, X u ω = X' u ω) ∧
    (∀ X : I → Ω → Cd T d,
      IsGraphonSolution P μ0 X0 B noise G b σ X →
      (⨆ u, ∫⁻ ω, ‖X u ω‖ₑ ^ (2 + ε) ∂P) < ⊤) := by sorry

end GraphonMF.Stability
