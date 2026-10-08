-- Prove2me | Theorems.Thm_GraphonMF_SparseLLN_lemma_7_1
-- name    : GraphonMF.SparseLLN.lemma_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:45:04.068233+00:00
-- url     : https://prove2.me/theorems/dcc8a16e-a92a-4478-82ac-2a9b26e1bd01
-- title:
--   Lemma 7.1 — uniform moments of the coupling error
-- statement:
--   Assume Condition 4.1 and either Condition 4.2 or 4.3. Couple the percolated particle $X_i^n$ and the limiting particle $X_{i/n}$ through the same initial state and Brownian motion. For every natural-number exponent $k$, their pathwise error has a moment bound uniform over all systems and particles:
--
--   $$\sup_{n\ge1}\max_{1\le i\le n}\mathbb E\|X_i^n-X_{i/n}\|_{*,T}^{k}<\infty.$$
--
--   This moment control supports the later edge-error estimates.
--
--   **Formalization Note** The bound is stated as an existential real constant before the graphon and edge sequences and before $n$. The path norm is the uniform norm on continuous paths, and expectation is a lower integral.
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), p. 3610, Lemma 7.1; https://doi.org/10.1214/22-AAP1901

import Definitions.Def_GraphonMF_SparseLLN_Setting

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
set_option autoImplicit false

namespace GraphonMF.SparseLLN

/-- Lemma 7.1, p. 3610: all coupling-error moments are uniformly bounded. -/
theorem lemma_7_1
    {T : ℝ≥0} {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (hT : 0 < T) (hd : 0 < d)
    (P : Measure Ω) (X0 : GraphonMF.Stability.I → Ω → Vec d) (B : GraphonMF.Stability.I → ℝ≥0 → Ω → Vec d)
    (hnoise : NoiseSetting P X0 B)
    (G : GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (hG : GraphonMF.Stability.IsGraphon G)
    (b : Vec d → Vec d → Vec d) (σ : Vec d → Matrix (Fin d) (Fin d) ℝ)
    (β : ℕ → ℝ) (h41 : Cond41 (initialLaw P X0) b σ β)
    (X : GraphonMF.Stability.I → Ω → GraphonMF.Stability.Cd T d)
    (hX : IsGraphonSolution42 P X0 B hnoise G b σ X) :
    ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Gs : ℕ → GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ)
        (ξ : (n : ℕ) → Ω → Fin n → Fin n → ℝ)
        (hξ : ∀ n i j, Measurable (fun ω => ξ n ω i j)),
        (Cond42 P X0 B ξ Gs β G ∨ Cond43 P X0 B ξ β G) →
        ∀ n : ℕ, ∀ Xn : Fin n → Ω → GraphonMF.Stability.Cd T d,
          IsParticleSolution41 P X0 B hnoise ξ hξ β b σ n Xn →
          ∀ i : Fin n,
            (∫⁻ ω, ‖Xn i ω - X (GraphonMF.Stability.lab n i) ω‖ₑ ^ k ∂P) ≤ ENNReal.ofReal C := by sorry

end GraphonMF.SparseLLN
