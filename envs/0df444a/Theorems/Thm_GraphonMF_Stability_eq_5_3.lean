-- Prove2me | Theorems.Thm_GraphonMF_Stability_eq_5_3
-- name    : GraphonMF.Stability.eq_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:27:23.293213+00:00
-- url     : https://prove2.me/theorems/21c629b6-e8c7-4b16-9621-e897cdd403b1
-- title:
--   (5.3), squared reading — contraction estimate for frozen flows
-- statement:
--   Under Condition 2.1 and for a fixed graphon $G$, there is a constant $\kappa>0$ such that any two frozen-flow solutions $X^\mu,X^\nu$ driven by the same initial states and Brownian motions satisfy, for every $t\in[0,T]$,
--
--   $$[W^\mathcal M_{2,t}(\mathcal L(X^\mu),\mathcal L(X^\nu))]^2\le\kappa\int_0^t[W^\mathcal M_{2,s}(\mu,\nu)]^2\,ds.$$
--
--   The bound controls the law map associated with the frozen-flow equation and is used for well-posedness of the nonlinear system.
--
--   **Formalization Note** Display (5.3) is printed without squares, while its proof on p. 3599 establishes the squared estimate above. The constant is chosen before the input law families and time.
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), pp. 3598–3599, (5.3) and its proof

import Mathlib
import Definitions.Def_GraphonMF_Stability_Setting

open MeasureTheory
open scoped ENNReal NNReal

namespace GraphonMF.Stability

/-- The squared estimate proved for (5.3), pp. 3598–3599. -/
theorem eq_5_3 {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (T : ℝ≥0)
    (hT : 0 < T) (P : Measure Ω) (μ0 : I → Measure (State d))
    (X0 : I → Ω → State d) (B : I → ℝ≥0 → Ω → State d)
    (noise : NoiseSetting P μ0 X0 B)
    (b : State d → State d → State d)
    (σ : State d → State d → Matrix (Fin d) (Fin d) ℝ)
    (ε : ℝ) (hc : Cond21 ε μ0 b σ)
    (G : I → I → ℝ) (hG : IsGraphon G) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ (μ ν : I → Measure (Cd T d))
        (Xμ Xν : I → Ω → Cd T d),
        IsFrozenSolution P μ0 X0 B noise G b σ μ Xμ →
        IsFrozenSolution P μ0 X0 B noise G b σ ν Xν →
        ∀ t : ℝ≥0, t ≤ T →
          W2M t (law P Xμ) (law P Xν) ^ (2 : ℝ) ≤
            ENNReal.ofReal κ *
              ∫⁻ (s : ℝ) in Set.Icc 0 (t : ℝ),
                W2M s.toNNReal μ ν ^ (2 : ℝ) := by sorry

end GraphonMF.Stability
