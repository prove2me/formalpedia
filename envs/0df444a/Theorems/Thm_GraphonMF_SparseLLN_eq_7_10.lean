-- Prove2me | Theorems.Thm_GraphonMF_SparseLLN_eq_7_10
-- name    : GraphonMF.SparseLLN.eq_7_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:45:24.823812+00:00
-- url     : https://prove2.me/theorems/61c08632-b83d-4987-aa59-060b6f7a679e
-- title:
--   (7.10) — one-edge coupling estimate
-- statement:
--   Under Condition 4.1 and the step-graphon and Bernoulli-edge parts of Condition 4.2, put $e_j(s)=X_j^n(s)-X_{j/n}(s)$. For each $q>1$, a constant $\kappa(q)$ gives, for every $n,i,j$ and $s\in[0,T]$,
--
--   $$\mathbb E[\xi^n_{ij}|e_j(s)|^2]\le\left(2\mathbb E|e_j(s)|^2+\frac{\kappa(q)}{(n\beta_n)^{1/q}}\right)\beta_nG_n(i/n,j/n).$$
--
--   This estimates how strongly a sampled edge can bias the squared coupling error at its endpoint.
--
--   **Formalization Note** The estimate includes diagonal edges $i=j$, as printed. The edge law includes self-loops and independence from all initial states and Brownian motions. The constant is chosen before the edge sequence and particle count.
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), p. 3614, (7.10); https://doi.org/10.1214/22-AAP1901

import Definitions.Def_GraphonMF_SparseLLN_Setting

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
set_option autoImplicit false

namespace GraphonMF.SparseLLN

/-- Equation (7.10), p. 3614: one sampled edge is nearly independent of the coupling error. -/
theorem eq_7_10
    {T : ℝ≥0} {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (hT : 0 < T) (hd : 0 < d)
    (P : Measure Ω) (X0 : GraphonMF.Stability.I → Ω → Vec d) (B : GraphonMF.Stability.I → ℝ≥0 → Ω → Vec d)
    (hnoise : NoiseSetting P X0 B)
    (G : GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (hG : GraphonMF.Stability.IsGraphon G)
    (b : Vec d → Vec d → Vec d) (σ : Vec d → Matrix (Fin d) (Fin d) ℝ)
    (β : ℕ → ℝ) (h41 : Cond41 (initialLaw P X0) b σ β)
    (X : GraphonMF.Stability.I → Ω → GraphonMF.Stability.Cd T d)
    (hX : IsGraphonSolution42 P X0 B hnoise G b σ X) :
    ∀ q : ℝ, 1 < q → ∃ κq : ℝ, 0 ≤ κq ∧
      ∀ (Gs : ℕ → GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ)
        (ξ : (n : ℕ) → Ω → Fin n → Fin n → ℝ)
        (hξ : ∀ n i j, Measurable (fun ω => ξ n ω i j)),
        Cond42ab P X0 B ξ Gs β →
        ∀ n : ℕ, ∀ Xn : Fin n → Ω → GraphonMF.Stability.Cd T d,
          IsParticleSolution41 P X0 B hnoise ξ hξ β b σ n Xn →
          ∀ i j : Fin n, ∀ s : ℝ≥0, s ≤ T →
            (∫⁻ ω, ENNReal.ofReal (ξ n ω i j) *
              ‖atTime (Xn j ω) s - atTime (X (GraphonMF.Stability.lab n j) ω) s‖ₑ ^ 2 ∂P) ≤
            (2 * (∫⁻ ω, ‖atTime (Xn j ω) s - atTime (X (GraphonMF.Stability.lab n j) ω) s‖ₑ ^ 2 ∂P) +
              ENNReal.ofReal (κq / (((n : ℝ) * β n) ^ (1 / q)))) *
            ENNReal.ofReal (β n * Gs n (GraphonMF.Stability.lab n i) (GraphonMF.Stability.lab n j)) := by sorry

end GraphonMF.SparseLLN
