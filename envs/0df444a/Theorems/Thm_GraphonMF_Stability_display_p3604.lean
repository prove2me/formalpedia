-- Prove2me | Theorems.Thm_GraphonMF_Stability_display_p3604
-- name    : GraphonMF.Stability.display_p3604
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:27:43.594211+00:00
-- url     : https://prove2.me/theorems/870f6e30-f2e4-4996-94db-540a453c3014
-- title:
--   §5.2, p. 3604 — quantitative graphon stability bound
-- statement:
--   Fix a graphon $G$ and its solution $X^G$ under Condition 2.1. There is $\kappa>0$ such that for each $M>0$ there is $\kappa(M)>0$, uniform over comparison graphons $G'$ and their solutions, with
--
--   $$\int_I[W_{2,t}(\mu^{G'}_u,\mu^G_u)]^2\,du\le\kappa\bigl(M^{-\varepsilon}+\kappa(M)\|G'-G\|_{\infty\to1}\bigr),\qquad 0\le t\le T.$$
--
--   The estimate separates the moment truncation error from the difference between interaction kernels. It is the quantitative step used to obtain Theorem 2.1(c).
--
--   **Formalization Note** The page writes $G_n$; the bound uses only the comparison graphon and its solution, so the formal statement quantifies over any $G'$. The constants are chosen before $G'$ and $t$.
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), p. 3604, §5.2, first display

import Mathlib
import Definitions.Def_GraphonMF_Stability_Setting

open MeasureTheory
open scoped ENNReal NNReal

namespace GraphonMF.Stability

/-- The quantitative stability bound at the top of p. 3604. -/
theorem display_p3604 {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (T : ℝ≥0)
    (hT : 0 < T) (P : Measure Ω) (μ0 : I → Measure (State d))
    (X0 : I → Ω → State d) (B : I → ℝ≥0 → Ω → State d)
    (noise : NoiseSetting P μ0 X0 B)
    (b : State d → State d → State d)
    (σ : State d → State d → Matrix (Fin d) (Fin d) ℝ)
    (ε : ℝ) (hc : Cond21 ε μ0 b σ)
    (G : I → I → ℝ) (hG : IsGraphon G)
    (X : I → Ω → Cd T d)
    (hX : IsGraphonSolution P μ0 X0 B noise G b σ X) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ M : ℝ, 0 < M → ∃ κM : ℝ, 0 < κM ∧
      ∀ (G' : I → I → ℝ) (X' : I → Ω → Cd T d),
        IsGraphon G' → IsGraphonSolution P μ0 X0 B noise G' b σ X' →
        ∀ t : ℝ≥0, t ≤ T →
          (∫⁻ u, W2t t (law P X' u) (law P X u) ^ (2 : ℝ)) ≤
            ENNReal.ofReal (κ * (1 / M ^ ε + κM *
              opNorm (fun u v => G' u v - G u v))) := by sorry

end GraphonMF.Stability
