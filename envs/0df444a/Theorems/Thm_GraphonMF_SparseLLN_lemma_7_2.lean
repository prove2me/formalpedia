-- Prove2me | Theorems.Thm_GraphonMF_SparseLLN_lemma_7_2
-- name    : GraphonMF.SparseLLN.lemma_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:44:42.007433+00:00
-- url     : https://prove2.me/theorems/67ad17da-ef47-4dcb-be52-9067e65e6c44
-- title:
--   Lemma 7.2 — mean-square coupling bound
-- statement:
--   Assume Conditions 2.2 and 4.1, and the step-graphon and Bernoulli-edge parts 4.2(a,b). There is a positive constant $\kappa$ and, for every $M>0$, a positive constant $\kappa(M)$, both independent of the sequences $(G_n)$ and $(\xi^n)$, such that
--
--   $$\limsup_{n\to\infty}\frac1n\sum_{i=1}^{n}\mathbb E\|X_i^n-X_{i/n}\|_{*,T}^{2}\le\kappa(M)\limsup_{n\to\infty}\|G_n-G\|_{\infty\to1}+\frac{\kappa}{M^2}.$$
--
--   The bound relates the particle coupling error to graphon approximation and a truncation parameter. It is the quantitative input for the second clause of Theorem 4.1.
--
--   **Formalization Note** The general constant $\kappa$ precedes $M$; $\kappa(M)$ may depend on $M$, and both are uniform over the graphon and edge sequences. Condition 4.2(c), convergence in cut norm, is absent, as in the lemma. Extended nonnegative limsups represent the nonnegative expectations.
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), p. 3610, Lemma 7.2; https://doi.org/10.1214/22-AAP1901

import Definitions.Def_GraphonMF_SparseLLN_Setting

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
set_option autoImplicit false

namespace GraphonMF.SparseLLN

/-- Lemma 7.2, p. 3610: mean-square coupling error controlled by operator-norm graphon discrepancy. -/
theorem lemma_7_2
    {T : ℝ≥0} {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (hT : 0 < T) (hd : 0 < d)
    (P : Measure Ω) (X0 : GraphonMF.Stability.I → Ω → Vec d) (B : GraphonMF.Stability.I → ℝ≥0 → Ω → Vec d)
    (hnoise : NoiseSetting P X0 B)
    (G : GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (hG : GraphonMF.Stability.IsGraphon G)
    (b : Vec d → Vec d → Vec d) (σ : Vec d → Matrix (Fin d) (Fin d) ℝ)
    (β : ℕ → ℝ) (h41 : Cond41 (initialLaw P X0) b σ β)
    (N : ℕ) (J : Fin N → Set GraphonMF.Stability.I)
    (h22a : Cond22a (initialLaw P X0) J) (h22b : Cond22b G J)
    (X : GraphonMF.Stability.I → Ω → GraphonMF.Stability.Cd T d)
    (hX : IsGraphonSolution42 P X0 B hnoise G b σ X) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ M : ℝ, 0 < M → ∃ κM : ℝ, 0 < κM ∧
      ∀ (Gs : ℕ → GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ)
        (ξ : (n : ℕ) → Ω → Fin n → Fin n → ℝ)
        (hξ : ∀ n i j, Measurable (fun ω => ξ n ω i j)),
        Cond42ab P X0 B ξ Gs β →
        ∀ Xn : (n : ℕ) → Fin n → Ω → GraphonMF.Stability.Cd T d,
          (∀ n, IsParticleSolution41 P X0 B hnoise ξ hξ β b σ n (Xn n)) →
          limsup (fun n => errorAvg P X n (Xn n)) atTop ≤
            ENNReal.ofReal κM *
              limsup (fun n => ENNReal.ofReal (GraphonMF.Stability.opNorm
                (fun u v => Gs n u v - G u v))) atTop +
              ENNReal.ofReal (κ / M ^ 2) := by sorry

end GraphonMF.SparseLLN
