-- Prove2me | Theorems.Thm_Hairer_model_germ_bound_of_dyadic_overlap
-- name    : Hairer.model_germ_bound_of_dyadic_overlap
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T20:13:58.320513+00:00
-- url     : https://prove2.me/theorems/29605e97-7bec-4c24-9f5f-4475f193a437
-- title:
--   Fine-scale compatibility of model germs on overlapping dyadic boxes
-- statement:
--   Let $s$ be a positive integer scaling, $(\Pi,\Gamma)$ a model of a regularity structure with test order $r$, and $f$ a modelled distribution of real order $\gamma$. For every compact set $K$, there is a constant $C_K\ge0$ with the following property.
--
--   Suppose $x,z\in K$ and $0<\delta\le1/4$. Assume the coordinate boxes of widths $\delta^{s_i}$ at $x$ and $(2\delta)^{s_i}$ at $z$ overlap: there exists $w$ such that
--   $$|w_i-x_i|\le\delta^{s_i},\qquad |w_i-z_i|\le(2\delta)^{s_i}\quad\text{for every }i.$$
--   Then every normalized test $\eta\in B^r_{s,0}$ satisfies
--   $$\left|\left\langle\Pi_xf(x)-\Pi_zf(z),S^\delta_{s,x}\eta\right\rangle\right|\le C_K\delta^\gamma.$$
--   This estimate controls differences of local model germs on overlaps of adjacent grid scales, with the test still taken at the fine scale. It is an auxiliary estimate for constructing reconstruction approximations.
-- source:
--   Derived local estimate for the reconstruction proof in M. Hairer, A theory of regularity structures (2014), Theorem 3.10 and equation (3.36), using the modelled increment bound (3.1) and elementary coordinate-box overlap geometry.

import Definitions.Def_Hairer_Model

set_option autoImplicit false
noncomputable section

namespace Hairer

theorem model_germ_bound_of_dyadic_overlap
    {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s) {γ : ℝ}
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f) :
    ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ K, ∀ z ∈ K, ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
        (∃ w : Pt d, (∀ i, |w i - x i| ≤ δ ^ s i) ∧
          (∀ i, |w i - z i| ≤ (2 * δ) ^ s i)) →
        ∀ η : Pt d → ℝ, IsTestBall s r η →
          |(Pi x (f x) - Pi z (f z)).eval (scaledTest s δ x η)| ≤ C * δ ^ γ := by sorry

end Hairer
