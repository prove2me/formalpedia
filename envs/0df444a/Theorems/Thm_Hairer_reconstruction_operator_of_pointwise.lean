-- Prove2me | Theorems.Thm_Hairer_reconstruction_operator_of_pointwise
-- name    : Hairer.reconstruction_operator_of_pointwise
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T15:57:44.209693+00:00
-- url     : https://prove2.me/theorems/8b760f7d-24d0-4937-bc65-3be9571ce65d
-- title:
--   A linear reconstruction operator from pointwise existence
-- statement:
--   Fix a model map $\Pi_x$, a reexpansion map $\Gamma_{xy}$, a scaling $s$, a test order $r$, and real orders $\alpha,\gamma$. Suppose every modelled distribution $f\in\mathcal D^\gamma$ admits some distribution $\xi\in\mathcal C_s^\alpha$ with the local reconstruction estimate
--   $$\left|\langle\xi-\Pi_x f(x),S^\delta_{s,x}\eta\rangle\right|\le C_K\delta^\gamma.$$
--   The bound is uniform for $x$ in a compact set $K$, scales $0<\delta\le1$, and normalized smooth test functions of order $r$.
--
--   Then these reconstructions can be chosen by a single map $R$ whose restriction to $\mathcal D^\gamma$ is linear, with $Rf\in\mathcal C_s^\alpha$ and the same type of local reconstruction estimate for every $f$. No uniqueness or positivity of $\gamma$ is assumed. This reduces the algebraic choice-of-operator step to pointwise existence, including in the nonpositive-order regime; it does not establish that pointwise existence hypothesis.
-- source:
--   Algebraic reduction of the existence-of-operator step in M. Hairer, A theory of regularity structures (2014), Theorem 3.10. Auxiliary result, not a restatement of the full reconstruction theorem.

import Definitions.Def_Hairer_Model

set_option autoImplicit false

noncomputable section

namespace Hairer

theorem reconstruction_operator_of_pointwise
    {d : ℕ} {s : Fin d → ℕ} {α γ : ℝ}
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hex : ∀ f : Pt d → ModelSpace A E, IsModelled s γ Gam f →
      ∃ ξ : Distrib d, MemCalpha s α ξ ∧
        ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, ∀ x ∈ K,
          ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ η : Pt d → ℝ, IsTestBall s r η →
            |(ξ - Pi x (f x)).eval (scaledTest s δ x η)| ≤ C * δ ^ γ) :
    ∃ R : (Pt d → ModelSpace A E) → Distrib d,
      (∀ f g : Pt d → ModelSpace A E, IsModelled s γ Gam f → IsModelled s γ Gam g →
        R (f + g) = R f + R g) ∧
      (∀ (c : ℝ) (f : Pt d → ModelSpace A E), IsModelled s γ Gam f →
        R (c • f) = c • R f) ∧
      (∀ f : Pt d → ModelSpace A E, IsModelled s γ Gam f →
        MemCalpha s α (R f) ∧
        ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, ∀ x ∈ K,
          ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ η : Pt d → ℝ, IsTestBall s r η →
            |(R f - Pi x (f x)).eval (scaledTest s δ x η)| ≤ C * δ ^ γ) := by sorry

end Hairer
