-- Prove2me | Theorems.Thm_Hairer_reconstruction_estimate_exists
-- name    : Hairer.reconstruction_estimate_exists
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T21:03:38.794004+00:00
-- url     : https://prove2.me/theorems/bb4204f0-9e95-4a0d-a856-762a6c32f184
-- title:
--   Existence of a distribution satisfying the reconstruction estimate
-- statement:
--   Let $(A,T,G)$ be a regularity structure, let $(\Pi,\Gamma)$ be a model with normalized test ball of order $r$, and let $f$ be a modelled distribution of regularity $\gamma>0$. There exists a linear distribution $R$ such that, for every compact set $K$, there is a constant $C_K\ge0$ satisfying
--
--   $$
--   \left|\langle R-\Pi_xf(x),\eta_x^\rho\rangle\right|\le C_K\rho^\gamma
--   \qquad
--   (x\in K,\quad 0<\rho\le1,\quad \eta\in\mathcal B_s^r).
--   $$
--
--   Here $\eta_x^\rho$ denotes the anisotropically rescaled test centered at $x$. The constant is uniform over the center, scale, and normalized test. This establishes the existence and local error estimate in the reconstruction theorem. Membership in the negative Hölder class and uniqueness are separate conclusions and are not asserted here.
-- source:
--   Existence and local error estimate in M. Hairer, A theory of regularity structures (2014), Theorem 3.10, for positive modelled regularity.

import Definitions.Def_Hairer_Model
open BigOperators Hairer
noncomputable section

theorem Hairer.reconstruction_estimate_exists
    {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s) {γ : ℝ} (hγ : 0 < γ)
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f) :
    ∃ R : Distrib d,
      ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, 0 ≤ C ∧
        ∀ x ∈ K, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
        ∀ η : Pt d → ℝ, IsTestBall s r η →
        |(R - Pi x (f x)).eval (scaledTest s ρ x η)| ≤ C * ρ ^ γ := by sorry
