-- Prove2me | Theorems.Thm_GraphonMF_Stability_eq_5_2
-- name    : GraphonMF.Stability.eq_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:27:20.534977+00:00
-- url     : https://prove2.me/theorems/48724ae7-3c0b-4d1e-b487-2dbd1b7ba81b
-- title:
--   (5.2) — existence of a frozen-flow solution
-- statement:
--   Fix a graphon $G$, coefficients and initial laws satisfying Condition 2.1, and the common family of initial states and Brownian motions. For every prescribed path-law family $\mu\in\mathcal M$, the frozen-flow equation (5.1) has a pathwise solution $X^\mu$, and its family of path laws belongs to $\mathcal M$:
--
--   $$\forall\mu\in\mathcal M,\quad\exists X^\mu\text{ solving (5.1) with }(\mathcal L(X^\mu_u))_{u\in I}\in\mathcal M.$$
--
--   This makes the paper's law map $\Phi$ well defined on $\mathcal M$.
--
--   **Formalization Note** A solution is a continuous-path process satisfying the referenced Itô-process predicate for each label's natural filtration. Its nested drift and diffusion integrals are required to be integrable.
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), p. 3598, §5.1, (5.1)–(5.2)

import Mathlib
import Definitions.Def_GraphonMF_Stability_Setting

open MeasureTheory
open scoped NNReal

namespace GraphonMF.Stability

/-- Equation (5.2), p. 3598: a frozen flow has a pathwise solution whose law belongs to M. -/
theorem eq_5_2 {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (T : ℝ≥0)
    (hT : 0 < T) (P : Measure Ω) (μ0 : I → Measure (State d))
    (X0 : I → Ω → State d) (B : I → ℝ≥0 → Ω → State d)
    (noise : NoiseSetting P μ0 X0 B)
    (b : State d → State d → State d)
    (σ : State d → State d → Matrix (Fin d) (Fin d) ℝ)
    (ε : ℝ) (hc : Cond21 ε μ0 b σ)
    (G : I → I → ℝ) (hG : IsGraphon G) :
    ∀ μ : I → Measure (Cd T d), InM μ →
      ∃ X : I → Ω → Cd T d,
        IsFrozenSolution P μ0 X0 B noise G b σ μ X ∧ InM (law P X) := by sorry

end GraphonMF.Stability
