-- Prove2me | Theorems.Thm_Hairer_uniform_scaled_grid_increment_bound
-- name    : Hairer.uniform_scaled_grid_increment_bound
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T20:44:38.619985+00:00
-- url     : https://prove2.me/theorems/10882e04-12a2-4802-83ab-2072ab7322ae
-- title:
--   Uniform adjacent-grid estimate on rescaled tests
-- statement:
--   Let $f$ be a modelled distribution of regularity $\gamma$ for a regularity structure and model, and write $F_x=\Pi_xf(x)$. Using the tensor-product smooth-transition partition at scale $\delta$, define
--   $$
--   R_\delta\varphi=\sum_j\langle F_{x_j^\delta},\psi_j^\delta\varphi\rangle.
--   $$
--   For every compact set $K$, there exists $C\ge0$ such that
--   $$
--   \left|(R_\delta-R_{2\delta})(S^\rho_{s,x}\eta)\right|\le C\delta^\gamma
--   $$
--   for every $x\in K$, every normalized test $\eta\in B^r_{s,0}$, and every pair of scales satisfying $0<\delta\le\rho\le1$ and $\delta\le1/4$. The constant is independent of the test, its centre in $K$, and both scales. The estimate holds for every real $\gamma$.
--
--   For positive $\gamma$, this estimate controls the dyadic tail uniformly over rescaled tests. It strengthens convergence on each fixed test and supplies the fine-scale part of the local reconstruction argument.
-- source:
--   Auxiliary estimate for the construction in M. Hairer, A theory of regularity structures (2014), Theorem 3.10. The explicit smooth-transition grid and its uniform adjacent-scale estimate are part of this formalization.

import Definitions.Def_Hairer_Model
open BigOperators Hairer
noncomputable section

theorem Hairer.uniform_scaled_grid_increment_bound
    {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s) {γ : ℝ}
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f)
    (K : Set (Pt d)) (hK : IsCompact K) :
    let W : Pt d → ℝ := fun z ↦
      ∏ i, (Real.smoothTransition (z i + 1) - Real.smoothTransition (z i))
    let X := fun (δ : ℝ) (j : Fin d → ℤ) (i : Fin d) ↦ δ ^ s i * (j i : ℝ)
    let R := fun (δ : ℝ) (φ : Pt d → ℝ) ↦ ∑ᶠ j : Fin d → ℤ,
      (Pi (X δ j) (f (X δ j))).eval
        (fun y ↦ W (fun i ↦ y i / δ ^ s i - (j i : ℝ)) * φ y)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      ∀ η : Pt d → ℝ, IsTestBall s r η →
      ∀ δ : ℝ, 0 < δ → δ ≤ ρ → δ ≤ 1 / 4 →
      |R δ (scaledTest s ρ x η) -
        R (2 * δ)
          (scaledTest s ρ x η)| ≤ C * δ ^ γ := by sorry
