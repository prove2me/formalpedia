-- Prove2me | Theorems.Thm_Hairer_dyadic_grid_limit_recon_bound
-- name    : Hairer.dyadic_grid_limit_recon_bound
-- status  : Proved
-- author  : @jmmaloney4
-- created : 2026-09-23T21:29:56.867901+00:00
-- url     : https://prove2.me/theorems/1589055b-0077-4222-bea2-c476db6523c8
-- title:
--   Reconstruction bound for the dyadic-grid limit ($\gamma>0$)
-- statement:
--   **Reconstruction bound for the dyadic smooth-grid limit, in the case $\gamma>0$.**
--
--   Let $(\Pi,\Gamma)$ be a model for a regularity structure with $\alpha=\min A<0$, and let $f\in\mathcal D^\gamma$ with $\gamma>0$. Let $R_n$ be the smooth-partition approximate reconstruction at scale $\delta_n=2^{-(n+2)}$, and let $\xi$ be the limiting distribution furnished by the Proved dyadic-grid limit lemma.
--
--   Then on every compact $K$ there is a constant $C$ such that for all $x\in K$, all $\rho\in(0,1/2]$, and all $\eta\in\mathcal B^r_{s,0}$,
--
--   $$
--   \bigl|(\xi-\Pi_x f(x))(S^\rho_{s,x}\eta)\bigr|\le C\,\rho^\gamma.
--   $$
--
--   Together with a matching $C^\alpha_s$ bound, this is the reconstruction estimate in Hairer's Theorem 3.10 (existence half for $\gamma>0$).
-- source:
--   M. Hairer, A theory of regularity structures, Invent. Math. 198 (2014), arXiv:1303.5113 (v4), proof of Theorem 3.10 (existence, γ>0); assembles Hairer.dyadic_grid_limit_exists with Hairer.uniform_grid_model_comparison

import Definitions.Def_Hairer_Model
set_option autoImplicit false
open scoped Classical DirectSum BigOperators Topology
open Filter BigOperators Hairer
noncomputable section

/-- Reconstruction bound for the dyadic smooth-grid limit (`γ > 0`). -/
theorem Hairer.dyadic_grid_limit_recon_bound
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
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f) :
    let W : Pt d → ℝ := fun z ↦
      ∏ i, (Real.smoothTransition (z i + 1) - Real.smoothTransition (z i))
    let δ : ℕ → ℝ := fun n ↦ (1 / 2 : ℝ) ^ (n + 2)
    let X := fun (n : ℕ) (j : Fin d → ℤ) (i : Fin d) ↦ δ n ^ s i * (j i : ℝ)
    let Rn := fun (n : ℕ) (φ : testFunctions d) ↦ ∑ᶠ j : Fin d → ℤ,
      (Pi (X n j) (f (X n j))).eval
        (fun y ↦ W (fun i ↦ y i / δ n ^ s i - (j i : ℝ)) * φ.val y)
    ∃ ξ : Distrib d,
      (∀ φ : testFunctions d, Tendsto (fun n ↦ Rn n φ) atTop (𝓝 (ξ φ))) ∧
      ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 2 →
        ∀ η : Pt d → ℝ, IsTestBall s r η →
          |(ξ - Pi x (f x)).eval (scaledTest s ρ x η)| ≤ C * ρ ^ γ := by
  sorry
