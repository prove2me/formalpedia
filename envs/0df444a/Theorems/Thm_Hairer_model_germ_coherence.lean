-- Prove2me | Theorems.Thm_Hairer_model_germ_coherence
-- name    : Hairer.model_germ_coherence
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T16:02:50.853414+00:00
-- url     : https://prove2.me/theorems/9484e0ec-456c-4088-9a6b-fe673ef91c98
-- title:
--   Local compatibility of model germs at a common test scale
-- statement:
--   Fix a regularity structure, a model $(\Pi,\Gamma)$, its test order $r$, and a modelled distribution $f$ of real order $\gamma$. On every compact set $K$ there is a constant $C_K$ such that
--   $$\left|\langle\Pi_x f(x)-\Pi_y f(y),S^\delta_{s,x}\eta\rangle\right|\le C_K\delta^\gamma$$
--   whenever $x,y\in K$, $0<\delta\le1$, the scaled distance between $x$ and $y$ is at most $\delta$, and $\eta$ is a normalized smooth test function of order $r$.
--
--   Thus the local distributions based at nearby points agree to order $\gamma$ when tested at a scale containing both points. This is a local compatibility estimate toward reconstruction; no reconstruction operator or test-order transfer is asserted.
-- source:
--   Auxiliary estimate in the reconstruction proof: M. Hairer, A theory of regularity structures (2014), proof of Theorem 3.10 and equation (3.36), specialized to base-point distance at most the test scale.

import Definitions.Def_Hairer_Model

set_option autoImplicit false
open BigOperators

noncomputable section

namespace Hairer

theorem model_germ_coherence
    {d : ℕ} {s : Fin d → ℕ} {γ : ℝ}
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f) :
    ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ,
      ∀ x ∈ K, ∀ y ∈ K, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → snorm s (x - y) ≤ δ →
        ∀ η : Pt d → ℝ, IsTestBall s r η →
          |(Pi x (f x) - Pi y (f y)).eval (scaledTest s δ x η)| ≤ C * δ ^ γ := by sorry

end Hairer
