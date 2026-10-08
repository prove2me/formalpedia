-- Prove2me | Theorems.Thm_GraphonMF_SparseLLN_eq_7_15
-- name    : GraphonMF.SparseLLN.eq_7_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:44:58.462674+00:00
-- url     : https://prove2.me/theorems/c1980748-c6c8-4cc8-aacf-f737e2e9e8b7
-- title:
--   (7.15) — bound on the second interaction-error term
-- statement:
--   Let $R_s^{n,2}$ be the second averaged squared drift difference in the decomposition (7.2), replacing $X_j^n(s)$ by $X_{j/n}(s)$ while retaining the sampled edge weights. Under Condition 4.1 and the step-graphon and Bernoulli-edge parts of Condition 4.2, for each $q>1$,
--
--   $$R_s^{n,2}\le\frac{\kappa}{n}\sum_{j=1}^{n}\mathbb E|X_j^n(s)-X_{j/n}(s)|^2+\frac{\kappa(q)}{(n\beta_n)^{1/q}},\qquad 0\le s\le T.$$
--
--   This is the error estimate that handles dependence between edge weights and particle states.
--
--   **Formalization Note** The constant $\kappa$ is selected before $q$, while $\kappa(q)$ may depend on $q$. Both precede the graphon and edge sequences and $n$.
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), pp. 3611, 3615, (7.2), (7.15); https://doi.org/10.1214/22-AAP1901

import Definitions.Def_GraphonMF_SparseLLN_Setting

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
set_option autoImplicit false

namespace GraphonMF.SparseLLN

/-- Equation (7.15), p. 3615: the second error term in (7.2). -/
theorem eq_7_15
    {T : ℝ≥0} {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (hT : 0 < T) (hd : 0 < d)
    (P : Measure Ω) (X0 : GraphonMF.Stability.I → Ω → Vec d) (B : GraphonMF.Stability.I → ℝ≥0 → Ω → Vec d)
    (hnoise : NoiseSetting P X0 B)
    (G : GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (hG : GraphonMF.Stability.IsGraphon G)
    (b : Vec d → Vec d → Vec d) (σ : Vec d → Matrix (Fin d) (Fin d) ℝ)
    (β : ℕ → ℝ) (h41 : Cond41 (initialLaw P X0) b σ β)
    (X : GraphonMF.Stability.I → Ω → GraphonMF.Stability.Cd T d)
    (hX : IsGraphonSolution42 P X0 B hnoise G b σ X) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ q : ℝ, 1 < q → ∃ κq : ℝ, 0 ≤ κq ∧
      ∀ (Gs : ℕ → GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ)
        (ξ : (n : ℕ) → Ω → Fin n → Fin n → ℝ)
        (hξ : ∀ n i j, Measurable (fun ω => ξ n ω i j)),
        Cond42ab P X0 B ξ Gs β →
        ∀ n : ℕ, ∀ Xn : Fin n → Ω → GraphonMF.Stability.Cd T d,
          IsParticleSolution41 P X0 B hnoise ξ hξ β b σ n Xn →
          ∀ s : ℝ≥0, s ≤ T →
            Rn2 P ξ β b X n Xn s ≤
              ENNReal.ofReal (κ / n) *
                (∑ j : Fin n,
                  ∫⁻ ω, ‖atTime (Xn j ω) s - atTime (X (GraphonMF.Stability.lab n j) ω) s‖ₑ ^ 2 ∂P) +
              ENNReal.ofReal (κq / (((n : ℝ) * β n) ^ (1 / q))) := by sorry

end GraphonMF.SparseLLN
