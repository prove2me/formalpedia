-- Prove2me | Theorems.Thm_GrayStability_gray_stability_fixing_stationary_points
-- name    : GrayStability.gray_stability_fixing_stationary_points
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-05T21:19:00.517222+00:00
-- url     : https://prove2.me/theorems/9c76ff14-4d7e-400c-a64c-6f193eea9ada
-- title:
--   Remark 2.21(3): the Gray isotopy fixes points where $\dot\alpha_t$ vanishes
-- statement:
--   Let $M=F^{-1}(0)\subset\mathbb{R}^n$ be a compact regular level and $\alpha_t$, $t\in[0,1]$, a smooth family of contact forms on $M$. Then there are an isotopy $\psi_t$ of $M$ and smooth functions $\lambda_t>0$ on $M$ with $\psi_t^*\alpha_t=\lambda_t\alpha_0$ on $TM$ for $t\in[0,1]$, such that in addition every point $p\in M$ with
--   $$\dot\alpha_t(p)=0\ \text{ on } T_pM\quad\text{for all } t\in[0,1]$$
--   satisfies $\psi_t(p)=p$ for all $t\in[0,1]$.
--
--   This relative version is the form used to prove neighbourhood theorems for submanifolds, where the forms already agree along the submanifold (Geiges, proof of Theorem 2.27, the neighbourhood theorem for isotropic submanifolds).
-- source:
--   Geiges, Contact geometry, Handbook of Differential Geometry Vol. II (2006) 315-382, https://arxiv.org/abs/math/0307242, Remark 2.21 (3), p. 15

import Definitions.Def_GrayStability_Basic

open scoped ContDiff

namespace GrayStability

/-- Geiges, Remark 2.21 (3): the Gray isotopy can be chosen so that every point `p ∈ M`
at which `α̇_t(p)` vanishes on `T_p M` for all `t ∈ [0, 1]` stays fixed. -/
theorem gray_stability_fixing_stationary_points {n c : ℕ} (F : E n → (Fin c → ℝ))
    (hF : IsCompactRegularLevel F) (α : ℝ → OneForm n) (hα : IsContactFamilyOn F α) :
    ∃ ψ : ℝ → E n → E n, IsIsotopyOf F ψ ∧
      (∃ lam : ℝ → E n → ℝ, ContDiff ℝ ∞ (fun p : ℝ × E n => lam p.1 p.2) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ levelSet F, 0 < lam t y) ∧
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ levelSet F, ∀ v ∈ tangentSpace F y,
          pullback (ψ t) (α t) y v = lam t y * α 0 y v) ∧
      ∀ p ∈ levelSet F,
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ tangentSpace F p, formTimeDeriv α t p v = 0) →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ψ t p = p := by sorry

end GrayStability
