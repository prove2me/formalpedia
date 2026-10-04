-- Prove2me | Theorems.Thm_Hairer_reconstruction_limit_bound_of_uniform_consistency
-- name    : Hairer.reconstruction_limit_bound_of_uniform_consistency
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-27T05:46:15.48966+00:00
-- url     : https://prove2.me/theorems/cf381da7-2e17-44b2-8ed4-609165e25a86
-- title:
--   Uniform reconstruction bound for the approximant limit from uniform consistency in Hairer's regularity structures
-- statement:
--   Uniform reconstruction bound for the approximant limit, from uniform consistency (Hairer 2014, Section 3.1). Given an approximant net $n \\mapsto \\mathrm{approx}(\\psi, n)$ built from atomic decompositions of test functions at dyadic scales $2^{-n}$, assume the per-test-function consistency estimate and the following uniform consistency: on every compact $K$ there is a constant $C$ such that every approximant of a rescaled test function $S^\\delta_{s,x}\\eta$ (with $x \\in K$, $\\delta \\in (0,1]$, $\\eta \\in B^r_{s,0}$) at dyadic scale $2^{-n}$ is within $C\\,\\max(2^{-n},\\delta)^\\gamma$ of the germ $\\langle \\Pi_x f(x), S^\\delta_{s,x}\\eta\\rangle$. If $\\mathrm{limval}(\\psi)$ is the pointwise limit of the net, then on every compact $K$ $$ \\left|\\mathrm{limval}(S^\\delta_{s,x}\\eta) - \\langle \\Pi_x f(x), S^\\delta_{s,x}\\eta\\rangle\\right| \\le C\\,\\delta^\\gamma $$ uniformly over $x \\in K$, $\\delta \\in (0,1]$, $\\eta \\in B^r_{s,0}$. Together with consistency this yields Hairer's reconstruction theorem (Theorem 3.10): the limit is the reconstructed distribution. Formalization Note: this repairs the earlier published `Hairer.reconstruction_limit_uniform_bound`, whose consistency hypothesis yielded only a per-test-function constant $C(\\varphi)$ while the conclusion needs $C$ uniform over $x \\in K$, $\\delta$ and $\\eta$ -- a gap the old statement could not close. The added uniform-consistency hypothesis closes exactly this gap; the remaining proof is a routine limit passage.
-- source:
--   M. Hairer, A theory of regularity structures, Invent. Math. 198 (2014), 269-504, arXiv:1303.5113, Section 3.1.

import Definitions.Def_Hairer_Model

set_option autoImplicit false

open scoped Classical DirectSum

noncomputable section

namespace Hairer

/-- **Uniform reconstruction bound for the approximant limit, from uniform
consistency (Hairer 2014, §3.1).**

Let `approx` be an approximant net: at each dyadic scale `2^{-n}`, the value
`approx ψ hψ n` is computed from some atomic decomposition of the test function
`ψ` into rescaled test balls. Assume the consistency estimate with coefficient
control holds (hypothesis `hcons`), and assume the uniform consistency estimate
`huniform`: on every compact `K` there is a constant `C` such that every
approximant of a rescaled test function `S^δ_{s,x}η` (with `x ∈ K`,
`δ ∈ (0,1]`, `η ∈ B^r_{s,0}`) at dyadic scale `2^{-n}` is within
`C·max(2^{-n},δ)^γ` of the germ `⟨Π_x f(x), S^δ_{s,x}η⟩`. Let `limval`
be the pointwise limit of the net (which exists by consistency and completeness
of `ℝ`). Then `limval` satisfies the uniform reconstruction bound: on every
compact `K` there is `C` with
`|limval(S^δ_{s,x}η) - ⟨Π_x f(x), S^δ_{s,x}η⟩| ≤ C δ^γ`
uniformly over `x ∈ K`, `δ ∈ (0,1]` and `η ∈ B^r_{s,0}`. Together with the
consistency estimate this yields the reconstruction theorem (Theorem 3.10):
the limit is the reconstructed distribution.

This statement repairs `Hairer.reconstruction_limit_uniform_bound`, whose
hypothesis `hcons` gave only a per-test-function constant `C(φ)` while the
conclusion needs `C` uniform over `x ∈ K`, `δ` and `η` — a gap the old
statement could not close. The added uniform-consistency hypothesis `huniform`
closes exactly this gap; the remaining proof is a routine limit passage. -/
theorem reconstruction_limit_bound_of_uniform_consistency
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
    (hcons : ∀ (φ : Pt d → ℝ) (hφ : φ ∈ testFunctions d),
      ∀ (K : Set (Pt d)) (M : ℝ), IsCompact K →
      ∃ C : ℝ,
      ∀ (δ δ' : ℝ) (p p' : ℕ)
        (x : Fin p → Pt d) (c : Fin p → ℝ) (η : Fin p → (Pt d → ℝ))
        (x' : Fin p' → Pt d) (c' : Fin p' → ℝ) (η' : Fin p' → (Pt d → ℝ)),
        0 < δ → δ ≤ 1 → 0 < δ' → δ' ≤ 1 →
        (∀ i, x i ∈ K) → (∀ i, x' i ∈ K) →
        (∑ i, |c i|) ≤ M → (∑ i, |c' i|) ≤ M →
        (∀ i, IsTestBall s r (η i)) → (∀ i, IsTestBall s r (η' i)) →
        (∀ y, φ y = ∑ i, c i * scaledTest s δ (x i) (η i) y) →
        (∀ y, φ y = ∑ i, c' i * scaledTest s δ' (x' i) (η' i) y) →
        |∑ i, c i * (Pi (x i) (f (x i))).eval (scaledTest s δ (x i) (η i))
         - ∑ i, c' i * (Pi (x' i) (f (x' i))).eval (scaledTest s δ' (x' i) (η' i))|
          ≤ C * (max δ δ') ^ γ)
    (huniform : ∀ (K : Set (Pt d)), IsCompact K → ∃ C : ℝ,
      ∀ (x : Pt d), x ∈ K → ∀ (δ : ℝ), ∀ hδ : 0 < δ, ∀ _ : δ ≤ 1,
      ∀ (η : Pt d → ℝ), ∀ hη : IsTestBall s r η, ∀ (n : ℕ),
        |approx (scaledTest s δ x η)
            (scaledTest_mem s hδ x ⟨hη.smooth, hη.compactSupport⟩) n
         - (Pi x (f x)).eval (scaledTest s δ x η)|
          ≤ C * (max ((2 : ℝ) ^ (-(n : ℤ))) δ) ^ γ)
    (limval : (ψ : Pt d → ℝ) → ψ ∈ testFunctions d → ℝ)
    (hlim : ∀ (ψ : Pt d → ℝ) (hψ : ψ ∈ testFunctions d),
      Filter.Tendsto (approx ψ hψ) Filter.atTop (nhds (limval ψ hψ))) :
    ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, ∀ (x : Pt d), x ∈ K →
      ∀ (δ : ℝ), ∀ hδ : 0 < δ, ∀ _ : δ ≤ 1, ∀ (η : Pt d → ℝ), ∀ hη : IsTestBall s r η,
        |limval (scaledTest s δ x η) (scaledTest_mem s hδ x ⟨hη.smooth, hη.compactSupport⟩)
          - (Pi x (f x)).eval (scaledTest s δ x η)| ≤ C * δ ^ γ := by
  sorry

end Hairer
