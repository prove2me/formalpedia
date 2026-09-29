-- Prove2me | Theorems.Thm_Hairer_reconstruction_uniqueness
-- name    : Hairer.reconstruction_uniqueness
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T20:41:54.935147+00:00
-- url     : https://prove2.me/theorems/8f729de3-895e-4de8-8f65-02af614c87af
-- title:
--   Uniqueness in the reconstruction theorem
-- statement:
--   **Uniqueness clause of Hairer's Theorem 3.10.**
--
--   In the setting of the reconstruction theorem with $\gamma>0$, let $f \in \mathcal{D}^\gamma$
--   and suppose that two distributions $\xi$ and $\zeta$ both satisfy the reconstruction bound: for
--   every compact $K$ there is a constant $C$ with
--   $$ \big|(\xi - \Pi_x f(x))(S^{\delta}_{s,x}\eta)\big| \le C\,\delta^{\gamma}, \qquad
--   \big|(\zeta - \Pi_x f(x))(S^{\delta}_{s,x}\eta)\big| \le C\,\delta^{\gamma}, $$
--   uniformly over $x \in K$, $\delta \in (0,1]$ and $\eta \in \mathcal{B}^r_{s,0}$. Then
--   $\xi = \zeta$.
--
--   This is the part of Theorem 3.10 that does not require the wavelet construction: the difference
--   $\xi-\zeta$ is tested against localised test functions at scale $\delta$ and the resulting
--   $O(\delta^{\gamma})$ bound, with $\gamma>0$, forces it to vanish.
-- source:
--   M. Hairer, A theory of regularity structures, Inventiones Mathematicae 198 (2014) 269-504, arXiv:1303.5113 (v4), Theorem 3.10 (uniqueness clause) and its proof on p. 32-33

import Definitions.Def_Hairer_Model

set_option autoImplicit false

open scoped Classical DirectSum

noncomputable section

namespace Hairer

/-- **Theorem 3.10 (uniqueness clause), Hairer 2014.**

If `γ > 0`, the bound (3.3) determines the reconstruction of a modelled distribution
uniquely: two distributions that are both approximated by the jets `Π_x f(x)` to order
`δ^γ` on every compact set coincide. -/
theorem reconstruction_uniqueness
    {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s)
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {γ : ℝ} (hγ : 0 < γ)
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f)
    (ξ ζ : Distrib d)
    (hξ : ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ η : Pt d → ℝ, IsTestBall s r η →
        |(ξ - Pi x (f x)).eval (scaledTest s δ x η)| ≤ C * δ ^ γ)
    (hζ : ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ η : Pt d → ℝ, IsTestBall s r η →
        |(ζ - Pi x (f x)).eval (scaledTest s δ x η)| ≤ C * δ ^ γ) :
    ξ = ζ := by
  sorry

end Hairer
