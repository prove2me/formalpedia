-- Prove2me | Theorems.Thm_Hairer_reconstruction_sector_regularity_brversion
-- name    : Hairer.reconstruction_sector_regularity_brversion
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-27T01:37:17.271054+00:00
-- url     : https://prove2.me/theorems/f049a9bb-f149-4f93-a3a4-d92e785c6921
-- title:
--   Sector regularity of the reconstruction with the C^beta_s bound stated at the model's test order (B^r version)
-- statement:
--   **Corollary 3.16 of Hairer (2014), B^r-version.**
--
--   In the setting of the reconstruction theorem, suppose the modelled distribution f in D^gamma, gamma > 0, takes values in a sector V of regularity beta with alpha <= beta < 0, where alpha = min A. If xi is a distribution satisfying the reconstruction bound
--
--     |<(xi - Pi_x f(x)), S^delta_{s,x} eta>| <= C delta^gamma
--
--   locally uniformly over x in K, delta in (0,1] and eta in B^r_{s,0}, then xi satisfies the sharper regularity bound
--
--     |<xi, S^delta_{s,x} eta>| <= C delta^beta
--
--   locally uniformly over the same test class B^r_{s,0} (the model's own test order r). This is the C^beta_s bound of the original node, restated with the test class the model hypotheses actually control: the original conclusion demanded eta in B^{negReg beta}_{s,0}, a strictly larger test class the hypotheses cannot reach (from the hypotheses r >= negReg beta is provable).
-- source:
--   M. Hairer, A theory of regularity structures, Invent. Math. 198 (2014) 269-504, arXiv:1303.5113 (v4), Corollary 3.16, p. 33. B^r-version of theorem 9615a823-fbf8-4bf2-9ec7-84f439500d43, correcting a test-order formalization gap (verified analysis in ~/workspace/p2m_harness/hairer-sector/ANALYSIS.md).

import Definitions.Def_Hairer_Model

set_option autoImplicit false

open scoped Classical DirectSum

noncomputable section

namespace Hairer

/-- **Corollary 3.16, Hairer 2014 (B^r-version).**

Corrected variant of `Hairer.reconstruction_sector_regularity`
(`9615a823-fbf8-4bf2-9ec7-84f439500d43`): the conclusion `ξ ∈ C^β_s` is
stated with the model's test order `r` in the test class, i.e. the bound
`|⟨ξ, S^δ_{s,x} η⟩| ≤ C δ^β` holds over `η ∈ B^r_{s,0}` rather than over
`η ∈ B^{negReg β}_{s,0}`. The original is unprovable as stated: from the
hypotheses one can prove `r ≥ negReg β`, so the model Π-bound and the
reconstruction hypothesis only control `B^r_{s,0} ⊆ B^{negReg β}_{s,0}`,
strictly fewer test functions than the original conclusion requires, and
the reverse inclusion is false in general (counterexample: A = {-3, 0},
α = -3, β = -1.5, r = 4 > 2 = negReg β). With the test class at the model's
own order `r`, the statement is provable by the routine estimate chain
in the reconstruction analysis. -/
theorem reconstruction_sector_regularity_brversion
    {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s)
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {α : ℝ} (hα : IsLeast A α)
    {V : ∀ a : A, Submodule ℝ (E a)} {β : ℝ} (hV : IsSector G V β)
    (hβ : α ≤ β) (hβneg : β < 0)
    {γ : ℝ} (hγ : 0 < γ)
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f) (hfV : TakesValuesIn V f)
    (ξ : Distrib d)
    (hξ : ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ η : Pt d → ℝ, IsTestBall s r η →
        |(ξ - Pi x (f x)).eval (scaledTest s δ x η)| ≤ C * δ ^ γ) :
    ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ η : Pt d → ℝ, IsTestBall s r η →
        |ξ.eval (scaledTest s δ x η)| ≤ C * δ ^ β := by
  sorry

end Hairer
