-- Prove2me | Theorems.Thm_Hairer_multiplication
-- name    : Hairer.multiplication
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T20:59:43.279207+00:00
-- url     : https://prove2.me/theorems/03b7ecd9-509a-4d18-9a37-5eea7e95a507
-- title:
--   Products of modelled distributions (Hairer, Theorem 4.7)
-- statement:
--   **Theorem 4.7 of Hairer (2014), multiplication of modelled distributions.**
--
--   Let $\star$ be a product on $T$, let $V$ and $W$ be sectors of regularities $\alpha_1$ and
--   $\alpha_2$, and let $f_1 \in \mathcal{D}^{\gamma_1}(V)$ and $f_2 \in \mathcal{D}^{\gamma_2}(W)$
--   with $\gamma_1,\gamma_2>0$. Put
--   $$ \gamma = (\gamma_1+\alpha_2)\wedge(\gamma_2+\alpha_1). $$
--   If the pair $(V,W)$ is $\gamma$-regular, then the truncated pointwise product
--   $$ (f_1 \star_\gamma f_2)(x) = \sum_{m+n<\gamma} Q_m f_1(x) \star Q_n f_2(x) $$
--   is again a modelled distribution, of order $\gamma$.
--
--   This is the step that gives the theory a multiplication: two local expansions are multiplied
--   term by term and truncated at order $\gamma$, and the resulting family of jets is again
--   coherent in the sense of Definition 3.1. Note that the resulting order $\gamma$ is in general
--   smaller than $\gamma_1$ and $\gamma_2$ — multiplying by an object of negative homogeneity costs
--   regularity.
-- source:
--   M. Hairer, A theory of regularity structures, Inventiones Mathematicae 198 (2014) 269-504, arXiv:1303.5113 (v4), Theorem 4.7, p. 49, together with the truncated product (4.3)

import Definitions.Def_Hairer_Model

set_option autoImplicit false

open scoped Classical DirectSum

noncomputable section

namespace Hairer

/-- **Theorem 4.7 (Multiplication), Hairer 2014.**

Let `(V, W)` be sectors of regularities `α₁` and `α₂`, let `f₁ ∈ D^{γ₁}(V)` and
`f₂ ∈ D^{γ₂}(W)` with `γ₁, γ₂ > 0`, and set `γ = (γ₁ + α₂) ∧ (γ₂ + α₁)`. If the pair
`(V, W)` is `γ`-regular for the product `⋆`, then the truncated pointwise product
`f₁ ⋆_γ f₂`, given by `∑_{m+n<γ} Q_m f₁(x) ⋆ Q_n f₂(x)`, belongs to `D^γ`. -/
theorem multiplication
    {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s)
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {star : ModelSpace A E →ₗ[ℝ] ModelSpace A E →ₗ[ℝ] ModelSpace A E}
    (hstar : IsProduct one star)
    {V W : ∀ a : A, Submodule ℝ (E a)} {α₁ α₂ : ℝ}
    (hV : IsSector G V α₁) (hW : IsSector G W α₂)
    {γ₁ γ₂ γ : ℝ} (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hγ : γ = min (γ₁ + α₂) (γ₂ + α₁))
    (hreg : IsGammaRegular G V W star γ)
    {f₁ f₂ : Pt d → ModelSpace A E}
    (hf₁ : IsModelled s γ₁ Gam f₁) (hf₁V : TakesValuesIn V f₁)
    (hf₂ : IsModelled s γ₂ Gam f₂) (hf₂W : TakesValuesIn W f₂) :
    IsModelled s γ Gam (truncProd γ star f₁ f₂) := by
  sorry

end Hairer
