-- Prove2me | Theorems.Thm_Hairer_dyadic_grid_approx_cauchy
-- name    : Hairer.dyadic_grid_approx_cauchy
-- status  : Open
-- author  : @jmmaloney4
-- created : 2026-09-23T21:24:54.453981+00:00
-- url     : https://prove2.me/theorems/6880241c-311e-4991-ba8e-cf07206f3ee4
-- title:
--   Cauchy estimate for dyadic grid reconstruction approximants ($\gamma>0$)
-- statement:
--   **Cauchy estimate for the dyadic smooth-grid reconstruction approximants, in the case $\gamma>0$.**
--
--   Let $(\Pi,\Gamma)$ be a model for a regularity structure with $\alpha=\min A<0$, and let $f\in\mathcal D^\gamma$ with $\gamma>0$. Write $R_\delta$ for the smooth-partition approximate reconstruction that pairs each grid germ $\Pi_{x_j}f(x_j)$ against the tensor-product bump weight at anisotropic scale $\delta$ (the approximant appearing in the Proved lemma on uniform grid/model comparison).
--
--   Then on every compact $K$ there is a constant $C$ such that for all integers $n\le m$, all $x\in K$, and all test functions $\eta\in\mathcal B^r_{s,0}$,
--
--   $$
--   \bigl|(R_{2^{-n}}-R_{2^{-m}})(S^{2^{-m}}_{s,x}\eta)\bigr|
--   \le C\,2^{-n\gamma}.
--   $$
--
--   This is the Cauchy input needed to obtain the limiting reconstruction distribution in Hairer's Theorem 3.10 (existence half for $\gamma>0$).
-- source:
--   M. Hairer, A theory of regularity structures, Invent. Math. 198 (2014), arXiv:1303.5113 (v4), proof of Theorem 3.10 (existence, γ>0) via Prop. 3.25; smooth-grid form aligned with Prove2Me Hairer.uniform_grid_model_comparison

import Definitions.Def_Hairer_Model
import Definitions.Def_Hairer_GridWeight
set_option autoImplicit false
open scoped Classical DirectSum BigOperators
noncomputable section

namespace Hairer

/-- Approximate reconstruction pairing at scale `δ`. -/
def approxReconEval {d : ℕ} {A : Set ℝ} {E : A → Type}
    [∀ a : A, NormedAddCommGroup (E a)] [∀ a : A, NormedSpace ℝ (E a)]
    (s : Fin d → ℕ) (δ : ℝ)
    (Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d)
    (f : Pt d → ModelSpace A E) (φ : Pt d → ℝ) : ℝ :=
  ∑ᶠ j : Fin d → ℤ,
    (Pi (gridCentre s δ j) (f (gridCentre s δ j))).eval
      (fun y ↦ gridWeight (fun i ↦ y i / δ ^ s i - (j i : ℝ)) * φ y)

/-- Cauchy estimate for dyadic grid reconstruction approximants (`γ > 0`). -/
theorem dyadic_grid_approx_cauchy
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
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f)
    (K : Set (Pt d)) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n m : ℕ), n ≤ m → ∀ x ∈ K,
      ∀ η : Pt d → ℝ, IsTestBall s r η →
        |approxReconEval s (dyadicScale n) Pi f (scaledTest s (dyadicScale m) x η) -
          approxReconEval s (dyadicScale m) Pi f (scaledTest s (dyadicScale m) x η)| ≤
          C * (dyadicScale n) ^ γ := by
  sorry

end Hairer
