-- Prove2me | Theorems.Thm_Hairer_dyadic_grid_germ_sum_bound
-- name    : Hairer.dyadic_grid_germ_sum_bound
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T20:25:05.457276+00:00
-- url     : https://prove2.me/theorems/f983583d-95b6-435f-9f91-ad2aecc41751
-- title:
--   Uniform dyadic grid-overlap sum for model germs
-- statement:
--   Let $f$ be a modelled distribution of regularity $\gamma$ for a regularity structure and model, and write $F_x=\Pi_xf(x)$. Fix a compact set $K$ and a smooth compactly supported test function $\varphi$. For the tensor-product smooth-transition grid weights $\psi_j^\delta$ with centres $x_j^\delta$, there exists $C\ge0$ such that
--   $$
--   \sum_{j\in S}\sum_{k\in T}
--   \left|\left\langle F_{x_j^\delta}-F_{x_k^{2\delta}},
--   \psi_j^\delta\psi_k^{2\delta}\varphi\right\rangle\right|
--   \le C\delta^\gamma
--   $$
--   for every $0<\delta\le1/4$ and every pair of finite index sets $S,T$ whose selected centres lie in $K$. The constant is independent of the scale and index sets. The estimate holds for every real $\gamma$.
--
--   For positive regularity, this bound is summable along dyadic scales and supplies a quantitative ingredient for constructing the reconstruction operator. It is an auxiliary estimate, not a statement of the full reconstruction theorem.
-- source:
--   Auxiliary grid estimate for the reconstruction argument in M. Hairer, A theory of regularity structures (2014), Theorem 3.10; the explicit smooth-transition partition and finite-sum formulation are part of this formalization.

import Definitions.Def_Hairer_Model
open BigOperators Hairer
noncomputable section

theorem Hairer.dyadic_grid_germ_sum_bound
    {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s) {γ : ℝ}
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f)
    (K : Set (Pt d)) (hK : IsCompact K) (φ : Pt d → ℝ) (hφ : φ ∈ testFunctions d) :
    let W : Pt d → ℝ := fun z ↦
      ∏ i, (Real.smoothTransition (z i + 1) - Real.smoothTransition (z i))
    let ψ := fun (δ : ℝ) (j : Fin d → ℤ) (y : Pt d) ↦
      W (fun i ↦ y i / δ ^ s i - (j i : ℝ))
    let X := fun (δ : ℝ) (j : Fin d → ℤ) (i : Fin d) ↦ δ ^ s i * (j i : ℝ)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
      ∀ S T : Finset (Fin d → ℤ),
      (∀ j ∈ S, X δ j ∈ K) →
      (∀ k ∈ T, X (2 * δ) k ∈ K) →
      ∑ j ∈ S, ∑ k ∈ T,
        |(Pi (X δ j) (f (X δ j)) -
          Pi (X (2 * δ) k) (f (X (2 * δ) k))).eval
          (fun y ↦ ψ δ j y * ψ (2 * δ) k y * φ y)|
        ≤ C * δ ^ γ := by sorry
