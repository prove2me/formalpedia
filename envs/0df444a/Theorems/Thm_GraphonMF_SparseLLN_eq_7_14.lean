-- Prove2me | Theorems.Thm_GraphonMF_SparseLLN_eq_7_14
-- name    : GraphonMF.SparseLLN.eq_7_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:44:48.752421+00:00
-- url     : https://prove2.me/theorems/417fb688-d47c-417b-b06c-3e3b761100e9
-- title:
--   (7.14) — two-edge coupling estimate
-- statement:
--   Under Condition 4.1 and the step-graphon and Bernoulli-edge parts of Condition 4.2, let $j\ne k$ and $e_j(s)=X_j^n(s)-X_{j/n}(s)$. For each $q>1$ there is a constant $\kappa(q)$ such that
--
--   $$\mathbb E[\xi^n_{ij}\xi^n_{ik}|e_j(s)|\,|e_k(s)|]\le\left(\mathbb E|e_j(s)|^2+\mathbb E|e_k(s)|^2+\frac{\kappa(q)}{(n\beta_n)^{1/q}}\right)\beta_n^2G_n(i/n,j/n)G_n(i/n,k/n)$$
--
--   for every $n,i,j,k$ and $s\in[0,T]$. Together with the one-edge estimate, this controls the cross terms in a squared interaction sum.
--
--   **Formalization Note** The only index exclusion is the paper's $j\ne k$; either endpoint may equal $i$. Nonnegative expectations are lower integrals.
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), pp. 3614–3615, (7.14) and preceding index condition; https://doi.org/10.1214/22-AAP1901

import Definitions.Def_GraphonMF_SparseLLN_Setting

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
set_option autoImplicit false

namespace GraphonMF.SparseLLN

/-- Equation (7.14), p. 3615: the two-edge estimate for distinct endpoints. -/
theorem eq_7_14
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
          ∀ i j k : Fin n, j ≠ k → ∀ s : ℝ≥0, s ≤ T →
            (∫⁻ ω, ENNReal.ofReal (ξ n ω i j * ξ n ω i k) *
              ENNReal.ofReal (‖atTime (Xn j ω) s - atTime (X (GraphonMF.Stability.lab n j) ω) s‖) *
              ENNReal.ofReal (‖atTime (Xn k ω) s - atTime (X (GraphonMF.Stability.lab n k) ω) s‖) ∂P) ≤
            ((∫⁻ ω, ‖atTime (Xn j ω) s - atTime (X (GraphonMF.Stability.lab n j) ω) s‖ₑ ^ 2 ∂P) +
             (∫⁻ ω, ‖atTime (Xn k ω) s - atTime (X (GraphonMF.Stability.lab n k) ω) s‖ₑ ^ 2 ∂P) +
             ENNReal.ofReal (κq / (((n : ℝ) * β n) ^ (1 / q)))) *
            ENNReal.ofReal ((β n) ^ 2 * Gs n (GraphonMF.Stability.lab n i) (GraphonMF.Stability.lab n j) *
              Gs n (GraphonMF.Stability.lab n i) (GraphonMF.Stability.lab n k)) := by sorry

end GraphonMF.SparseLLN
