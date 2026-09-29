-- Prove2me | Theorems.Thm_Hairer_reconstruction_approximants_cauchy
-- name    : Hairer.reconstruction_approximants_cauchy
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-26T21:25:43.618996+00:00
-- url     : https://prove2.me/theorems/40f4ffe5-54e4-4efd-a658-28354c68676e
-- title:
--   Consistency of reconstruction approximants in Hairer's regularity structures
-- statement:
--   Consistency of the reconstruction approximants (key estimate of Hairer 2014, Section 3.1). For a regularity structure with model (Pi, Gam), least homogeneity alpha < 0, gamma > 0, and a modelled distribution f in D^gamma, the atomic approximants are consistent: any two atomic decompositions of the same test function at scales delta, delta' give values differing by at most C(phi) * max(delta,delta')^gamma. Hence the approximants form a Cauchy net and the limit is independent of decompositions. Analytic core of Hairer's reconstruction theorem (Theorem 3.10).
-- source:
--   M. Hairer, A theory of regularity structures, Invent. Math. 198 (2014), 269-504, arXiv:1303.5113, Section 3.1.

import Definitions.Def_Hairer_Model

set_option autoImplicit false

open scoped Classical DirectSum

noncomputable section

namespace Hairer

/-- **Consistency of reconstruction approximants (Hairer 2014, §3.1, key estimate).**

For `f ∈ D^γ` with `γ > 0`, the atomic approximants built from the model's germs
are consistent: evaluating the approximant
`∑ᵢ cᵢ ⟨Π_{xᵢ} f(xᵢ), S^δ_{s,xᵢ} ηᵢ⟩` on any two atomic decompositions
`φ = ∑ᵢ cᵢ S^δ_{s,xᵢ} ηᵢ` and `φ = ∑ⱼ c'ⱼ S^{δ'}_{s,x'ⱼ} η'ⱼ` of the same test
function `φ` at scales `δ, δ' ∈ (0,1]` gives values differing by at most
`C(φ)·max(δ,δ')^γ`. In particular the approximants form a Cauchy net as
`δ → 0`, and the limit is independent of the chosen decompositions. This is the
analytic core of the reconstruction theorem (Theorem 3.10); the proof is
Hairer's multiresolution estimate in §3.1. -/
theorem reconstruction_approximants_cauchy
    {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s)
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {α : ℝ} (hα : IsLeast A α) (hαneg : α < 0)
    {γ : ℝ} (hγ : 0 < γ)
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f) :
    ∀ (φ : Pt d → ℝ) (hφ : φ ∈ testFunctions d), ∃ C : ℝ,
      ∀ (δ δ' : ℝ) (n n' : ℕ)
        (x : Fin n → Pt d) (c : Fin n → ℝ) (η : Fin n → (Pt d → ℝ))
        (x' : Fin n' → Pt d) (c' : Fin n' → ℝ) (η' : Fin n' → (Pt d → ℝ)),
        0 < δ → δ ≤ 1 → 0 < δ' → δ' ≤ 1 →
        (∀ i, IsTestBall s r (η i)) → (∀ i, IsTestBall s r (η' i)) →
        (∀ y, φ y = ∑ i, c i * scaledTest s δ (x i) (η i) y) →
        (∀ y, φ y = ∑ i, c' i * scaledTest s δ' (x' i) (η' i) y) →
        |∑ i, c i * (Pi (x i) (f (x i))).eval (scaledTest s δ (x i) (η i))
         - ∑ i, c' i * (Pi (x' i) (f (x' i))).eval (scaledTest s δ' (x' i) (η' i))|
          ≤ C * (max δ δ') ^ γ := by
  sorry

end Hairer
