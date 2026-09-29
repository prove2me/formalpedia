-- Prove2me | Theorems.Thm_Hairer_reconstruction_sector_regularity
-- name    : Hairer.reconstruction_sector_regularity
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-12T20:45:01.48113+00:00
-- url     : https://prove2.me/theorems/9615a823-fbf8-4bf2-9ec7-84f439500d43
-- title:
--   Regularity of the reconstruction on a sector (Hairer, Corollary 3.16)
-- statement:
--   **Corollary 3.16 of Hairer (2014).**
--
--   In the setting of the reconstruction theorem, suppose the modelled distribution
--   $f \in \mathcal{D}^\gamma$, $\gamma>0$, takes values in a sector $V$ of regularity $\beta$
--   with $\alpha \le \beta < 0$, where $\alpha = \min A$. If $\xi$ satisfies the reconstruction
--   bound
--   $$ \big|(\xi - \Pi_x f(x))(S^{\delta}_{s,x}\eta)\big| \lesssim \delta^{\gamma} $$
--   locally uniformly, then $\xi \in \mathcal{C}^\beta_s$.
--
--   So the reconstruction of a modelled distribution is no rougher than the sector in which it
--   takes its values: the a priori regularity $\mathcal{C}^\alpha_s$ coming from the full model
--   improves to $\mathcal{C}^\beta_s$. This is the statement that justifies calling $\beta$ the
--   *regularity* of the sector.
-- source:
--   M. Hairer, A theory of regularity structures, Inventiones Mathematicae 198 (2014) 269-504, arXiv:1303.5113 (v4), Corollary 3.16, p. 33

import Definitions.Def_Hairer_Model

set_option autoImplicit false

open scoped Classical DirectSum

noncomputable section

namespace Hairer

/-- **Corollary 3.16, Hairer 2014.**

In the setting of the reconstruction theorem, if the modelled distribution `f ∈ D^γ`
(with `γ > 0`) takes values in a sector `V` of regularity `β ∈ [α, 0)`, where
`α = min A`, then its reconstruction belongs to the sharper space `C^β_s`. -/
theorem reconstruction_sector_regularity
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
    MemCalpha s β ξ := by
  sorry

end Hairer
