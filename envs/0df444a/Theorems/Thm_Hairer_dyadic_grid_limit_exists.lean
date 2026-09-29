-- Prove2me | Theorems.Thm_Hairer_dyadic_grid_limit_exists
-- name    : Hairer.dyadic_grid_limit_exists
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T20:34:26.299691+00:00
-- url     : https://prove2.me/theorems/fbe69d67-1f44-4c42-89c6-24bfb25dcc76
-- title:
--   Convergence of the dyadic reconstruction grid with geometric error
-- statement:
--   Let $f$ be a modelled distribution with positive regularity $\gamma$ for a regularity structure and model, and write $F_x=\Pi_xf(x)$. Use the tensor-product smooth-transition partition of unity at scales $\delta_n=2^{-(n+2)}$, with weights $\psi_j^{\delta_n}$ and centres $x_j^{\delta_n}$. For every smooth compactly supported test function $\varphi$, set
--   $$
--   R_n\varphi=\sum_j\langle F_{x_j^{\delta_n}},\psi_j^{\delta_n}\varphi\rangle.
--   $$
--   Only finitely many summands are nonzero. There exists a single linear distribution $R$ such that, for every such test,
--   $$
--   R_n\varphi\longrightarrow R\varphi,
--   \qquad
--   |R\varphi-R_n\varphi|\le C_\varphi\,2^{-n\gamma}
--   \quad(n\ge0)
--   $$
--   for some $C_\varphi\ge0$ independent of $n$.
--
--   This constructs the limit of the dyadic grid approximations. The constant may depend on the fixed test function; the uniform local estimate over rescaled tests needed for the full reconstruction theorem is a separate statement.
-- source:
--   Auxiliary construction for M. Hairer, A theory of regularity structures (2014), Theorem 3.10. This formalization uses a tensor-product smooth-transition grid and establishes its pointwise distributional limit with a geometric tail estimate.

import Definitions.Def_Hairer_Model
open BigOperators Filter Hairer
open scoped Topology
noncomputable section

theorem Hairer.dyadic_grid_limit_exists
    {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s) {γ : ℝ} (hγ : 0 < γ)
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f) :
    let W : Pt d → ℝ := fun z ↦
      ∏ i, (Real.smoothTransition (z i + 1) - Real.smoothTransition (z i))
    let δ : ℕ → ℝ := fun n ↦ (1 / 2 : ℝ) ^ (n + 2)
    let X := fun (n : ℕ) (j : Fin d → ℤ) (i : Fin d) ↦ δ n ^ s i * (j i : ℝ)
    let Rn := fun (n : ℕ) (φ : testFunctions d) ↦ ∑ᶠ j : Fin d → ℤ,
      (Pi (X n j) (f (X n j))).eval
        (fun y ↦ W (fun i ↦ y i / δ n ^ s i - (j i : ℝ)) * φ.val y)
    ∃ R : Distrib d,
      (∀ φ : testFunctions d, Tendsto
        (fun n ↦ Rn n φ) atTop (𝓝 (R φ))) ∧
      ∀ φ : testFunctions d, ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
        |R φ - Rn n φ| ≤
          C * ((1 / 2 : ℝ) ^ γ) ^ n := by sorry
