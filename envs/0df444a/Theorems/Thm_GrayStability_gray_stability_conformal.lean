-- Prove2me | Theorems.Thm_GrayStability_gray_stability_conformal
-- name    : GrayStability.gray_stability_conformal
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-05T21:01:05.812911+00:00
-- url     : https://prove2.me/theorems/7f022f6d-ff6f-4c9e-a03b-9648b54b69ca
-- title:
--   Theorem 2.20 (proof): Gray isotopy with $\psi_t^*\alpha_t=\lambda_t\alpha_0$
-- statement:
--   Let $M=F^{-1}(0)\subset\mathbb{R}^n$ be a compact regular level and $\alpha_t$, $t\in[0,1]$, a smooth family of contact forms on $M$. Then there are an isotopy $\psi_t$ of $M$ and a smooth function $\lambda:\mathbb{R}\times\mathbb{R}^n\to\mathbb{R}$, positive on $[0,1]\times M$, such that
--   $$\psi_t^*\alpha_t=\lambda_t\,\alpha_0\quad\text{on } T_yM,\qquad t\in[0,1],\ y\in M.$$
--
--   This is the form in which the proof of Gray's theorem produces the isotopy. It implies the theorem, since $\lambda_t>0$ gives $T\psi_t(\ker\alpha_0)=\ker\alpha_t$.
-- source:
--   Geiges, Contact geometry, Handbook of Differential Geometry Vol. II (2006) 315-382, https://arxiv.org/abs/math/0307242, proof of Theorem 2.20, pp. 14-15

import Definitions.Def_GrayStability_Basic

open scoped ContDiff

namespace GrayStability

/-- Geiges, proof of Theorem 2.20: for a smooth family of contact forms `α_t` on a
closed submanifold `M ⊂ ℝⁿ` there are an isotopy `ψ_t` of `M` and smooth positive
functions `λ_t` with `ψ_t^* α_t = λ_t α_0` on `TM`. -/
theorem gray_stability_conformal {n c : ℕ} (F : E n → (Fin c → ℝ))
    (hF : IsCompactRegularLevel F) (α : ℝ → OneForm n) (hα : IsContactFamilyOn F α) :
    ∃ ψ : ℝ → E n → E n, IsIsotopyOf F ψ ∧
      ∃ lam : ℝ → E n → ℝ, ContDiff ℝ ∞ (fun p : ℝ × E n => lam p.1 p.2) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ levelSet F, 0 < lam t y) ∧
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ levelSet F, ∀ v ∈ tangentSpace F y,
          pullback (ψ t) (α t) y v = lam t y * α 0 y v := by sorry

end GrayStability
