-- Prove2me | Theorems.Thm_Hairer_reconstruction_limit_uniform_bound
-- name    : Hairer.reconstruction_limit_uniform_bound
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-26T21:25:47.643984+00:00
-- url     : https://prove2.me/theorems/b3162054-0965-485f-9298-f25fb0c3e695
-- title:
--   Uniform reconstruction bound for the approximant limit in Hairer's regularity structures
-- statement:
--   Uniform reconstruction bound for the limit of the approximants (Hairer 2014, Section 3.1). Given an approximant net from atomic decompositions at dyadic scales satisfying the consistency estimate, its pointwise limit satisfies the uniform reconstruction bound: on every compact K, |limval(S^delta_{s,x} eta) - <Pi_x f(x), S^delta_{s,x} eta>| <= C delta^gamma uniformly over x in K, delta in (0,1], eta in B^r_{s,0}. Together with consistency this yields Hairer's reconstruction theorem (Theorem 3.10).
-- source:
--   M. Hairer, A theory of regularity structures, Invent. Math. 198 (2014), 269-504, arXiv:1303.5113, Section 3.1.

import Definitions.Def_Hairer_Model

set_option autoImplicit false

open scoped Classical DirectSum

noncomputable section

namespace Hairer

/-- **Uniform reconstruction bound for the approximant limit (Hairer 2014, §3.1).**

Let `approx` be an approximant net: at each dyadic scale `2^{-n}`, the value
`approx ψ hψ n` is computed from some atomic decomposition of the test function
`ψ` into rescaled test balls. Assume the consistency estimate
`reconstruction_approximants_cauchy` holds (hypothesis `hcons`), and let `limval`
be the pointwise limit of the net (which exists by consistency and completeness
of `ℝ`). Then `limval` satisfies the uniform reconstruction bound: on every
compact `K` there is `C` with
`|limval(S^δ_{s,x}η) - ⟨Π_x f(x), S^δ_{s,x}η⟩| ≤ C δ^γ`
uniformly over `x ∈ K`, `δ ∈ (0,1]` and `η ∈ B^r_{s,0}`. Together with the
consistency estimate this yields the reconstruction theorem (Theorem 3.10):
the limit is the reconstructed distribution. -/
theorem reconstruction_limit_uniform_bound
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
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f)
    (approx : (ψ : Pt d → ℝ) → ψ ∈ testFunctions d → ℕ → ℝ)
    (happrox : ∀ (ψ : Pt d → ℝ) (hψ : ψ ∈ testFunctions d) (n : ℕ),
      ∃ (m : ℕ) (x : Fin m → Pt d) (c : Fin m → ℝ) (η : Fin m → (Pt d → ℝ)),
        (∀ i, IsTestBall s r (η i)) ∧
        (∀ y, ψ y = ∑ i, c i * scaledTest s ((2 : ℝ) ^ (-(n : ℤ))) (x i) (η i) y) ∧
        approx ψ hψ n = ∑ i, c i * (Pi (x i) (f (x i))).eval
          (scaledTest s ((2 : ℝ) ^ (-(n : ℤ))) (x i) (η i)))
    (hcons : ∀ (φ : Pt d → ℝ) (hφ : φ ∈ testFunctions d), ∃ C : ℝ,
      ∀ (δ δ' : ℝ) (p p' : ℕ)
        (x : Fin p → Pt d) (c : Fin p → ℝ) (η : Fin p → (Pt d → ℝ))
        (x' : Fin p' → Pt d) (c' : Fin p' → ℝ) (η' : Fin p' → (Pt d → ℝ)),
        0 < δ → δ ≤ 1 → 0 < δ' → δ' ≤ 1 →
        (∀ i, IsTestBall s r (η i)) → (∀ i, IsTestBall s r (η' i)) →
        (∀ y, φ y = ∑ i, c i * scaledTest s δ (x i) (η i) y) →
        (∀ y, φ y = ∑ i, c' i * scaledTest s δ' (x' i) (η' i) y) →
        |∑ i, c i * (Pi (x i) (f (x i))).eval (scaledTest s δ (x i) (η i))
         - ∑ i, c' i * (Pi (x' i) (f (x' i))).eval (scaledTest s δ' (x' i) (η' i))|
          ≤ C * (max δ δ') ^ γ)
    (limval : (ψ : Pt d → ℝ) → ψ ∈ testFunctions d → ℝ)
    (hlim : ∀ (ψ : Pt d → ℝ) (hψ : ψ ∈ testFunctions d),
      Filter.Tendsto (approx ψ hψ) Filter.atTop (nhds (limval ψ hψ))) :
    ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, ∀ (x : Pt d), x ∈ K →
      ∀ (δ : ℝ), ∀ hδ : 0 < δ, ∀ _ : δ ≤ 1, ∀ (η : Pt d → ℝ), ∀ hη : IsTestBall s r η,
        |limval (scaledTest s δ x η) (scaledTest_mem s hδ x ⟨hη.smooth, hη.compactSupport⟩)
          - (Pi x (f x)).eval (scaledTest s δ x η)| ≤ C * δ ^ γ := by
  sorry

end Hairer
