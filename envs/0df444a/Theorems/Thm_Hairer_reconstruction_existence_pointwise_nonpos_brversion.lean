-- Prove2me | Theorems.Thm_Hairer_reconstruction_existence_pointwise_nonpos_brversion
-- name    : Hairer.reconstruction_existence_pointwise_nonpos_brversion
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-27T01:37:20.933085+00:00
-- url     : https://prove2.me/theorems/d7af3781-c2e4-4364-9991-333b67d0cfab
-- title:
--   Reconstruction existence for alpha < gamma <= 0 with the C^alpha_s bound stated at the model's test order (B^r version)
-- statement:
--   **Existence half of Hairer's Theorem 3.10 in the range alpha < gamma <= 0 (B^r-version), stated for one modelled distribution.**
--
--   Let T=(A,T,G) be a regularity structure, let (Pi,Gamma) be a model for it on R^d with scaling s and test order r, let alpha=min A < 0, and let alpha < gamma <= 0. Then for every modelled distribution f in D^gamma there exists a distribution xi such that
--
--     |<xi, S^delta_{s,x} eta>| <= C delta^alpha,    |<(xi-Pi_x f(x)), S^delta_{s,x} eta>| <= C delta^gamma,
--
--   the bounds holding, for every compact set K with constants C=C(K,f), uniformly over x in K, delta in (0,1] and all test functions eta in B^r_{s,0} (the model's own test class). The first bound is the C^alpha_s regularity claim stated at the model's test order r: this corrected variant replaces the test class B^{negReg alpha}_{s,0} of the original node, which the reconstruction construction cannot control (from the hypotheses r >= negReg alpha is provable). For gamma <= 0 the bound no longer determines xi, so no linearity in f is asserted.
-- source:
--   M. Hairer, A theory of regularity structures, Invent. Math. 198 (2014) 269-504, arXiv:1303.5113 (v4), Theorem 3.10, p. 31 (existence half in the non-positive range; construction in Section 3.1). B^r-version of theorem a1aef1ca-113d-4680-a38f-cf663cef85ba, correcting a test-order formalization gap (verified analysis in ~/workspace/p2m_harness/hairer_nonpos_triage.md).

import Definitions.Def_Hairer_Model

set_option autoImplicit false

open scoped Classical DirectSum

noncomputable section

namespace Hairer

/-- **Theorem 3.10, Hairer 2014 (B^r-version), in the case `α < γ ≤ 0`.**

Corrected variant of `Hairer.reconstruction_existence_pointwise_nonpos`
(`a1aef1ca-113d-4680-a38f-cf663cef85ba`): the regularity claim is stated
with the model's test order `r` in the test class, i.e. the `C^α_s` bound
holds over `η ∈ B^r_{s,0}` rather than over `η ∈ B^{negReg α}_{s,0}`.
The original is unprovable as stated: from the hypotheses one can prove
`r ≥ negReg α`, so the reconstruction construction only controls
`B^r_{s,0} ⊆ B^{negReg α}_{s,0}`, strictly fewer test functions than the
original conclusion requires, and the reverse inclusion is false in general.
With the test class at the model's own order `r`, the statement is provable
by the paper's §3.1 construction.

The range `γ ≤ α` is excluded because it is degenerate: there the only modelled
distribution is `f = 0`. -/
theorem reconstruction_existence_pointwise_nonpos_brversion
    {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s)
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {α : ℝ} (hα : IsLeast A α) (hαneg : α < 0)
    {γ : ℝ} (hγα : α < γ) (hγ : γ ≤ 0)
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f) :
    ∃ ξ : Distrib d,
      (∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        ∀ η : Pt d → ℝ, IsTestBall s r η →
          |ξ.eval (scaledTest s δ x η)| ≤ C * δ ^ α) ∧
      ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        ∀ η : Pt d → ℝ, IsTestBall s r η →
          |(ξ - Pi x (f x)).eval (scaledTest s δ x η)| ≤ C * δ ^ γ := by
  sorry

end Hairer
