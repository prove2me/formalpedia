-- Prove2me | Theorems.Thm_Hairer_reconstruction_exists_unique
-- name    : Hairer.reconstruction_exists_unique
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T21:14:09.325985+00:00
-- url     : https://prove2.me/theorems/dbbb4ff6-cb3f-4fb0-a08d-1954e5a530ac
-- title:
--   Existence and uniqueness for the reconstruction estimate
-- statement:
--   Let $(A,T,G)$ be a regularity structure, let $(\Pi,\Gamma)$ be a model with normalized test ball of order $r$, and let $f$ be a modelled distribution of regularity $\gamma>0$. There is exactly one linear distribution $\xi$ with the following property: for every compact set $K$, there exists a constant $C_K$ such that
--
--   $$
--   \left|\langle\xi-\Pi_x f(x),\eta_x^\delta\rangle\right|\le C_K\delta^\gamma
--   \qquad
--   (x\in K,\quad 0<\delta\le1,\quad \eta\in\mathcal B_s^r).
--   $$
--
--   Here $\eta_x^\delta$ is the anisotropically rescaled test centered at $x$. The estimate is uniform in the center, scale, and normalized test. This gives the existence and uniqueness assertions of the reconstruction theorem. The separate conclusion that $\xi$ belongs to the negative Hölder class at the least homogeneity is not included in this statement.
-- source:
--   Existence and uniqueness assertions of M. Hairer, A theory of regularity structures (2014), Theorem 3.10, for positive modelled regularity.

import Definitions.Def_Hairer_Model
open BigOperators Hairer
noncomputable section

theorem Hairer.reconstruction_exists_unique
    {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s) {γ : ℝ} (hγ : 0 < γ)
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f) :
    ∃! ξ : Distrib d, ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ,
      ∀ x ∈ K, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ η : Pt d → ℝ, IsTestBall s r η →
        |(ξ - Pi x (f x)).eval (scaledTest s δ x η)| ≤ C * δ ^ γ := by sorry
