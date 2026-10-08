-- Prove2me | Theorems.Thm_GrayStability_smooth_moser_lie_generator
-- name    : GrayStability.smooth_moser_lie_generator
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T15:38:16.603049+00:00
-- url     : https://prove2.me/theorems/a839e019-4445-451f-9fe9-8cd6444bb853
-- title:
--   Smooth compactly supported Moser generator for a contact family
-- statement:
--   Let $M=F^{-1}(0)\subset\mathbb R^n$ be a compact regular level of a globally smooth map, and let $\alpha_t$ be a jointly smooth family of ambient one-forms whose restrictions to $M$ are contact for $0\le t\le1$. There exist jointly smooth ambient families $X_t$ and $\mu_t$ and a compact set $K\subset\mathbb R^n$ such that $X_t=0$ outside $K$ for every real $t$, and, on $[0,1]\times M$,
--
--   $$X_t(y)\in T_yM\cap\ker\alpha_t(y),\qquad (\dot\alpha_t+\mathcal L_{X_t}\alpha_t)_y(v)=\mu_t(y)\alpha_t(y)(v)\quad(v\in T_yM).$$
--
--   This is the smooth generator stage of the Moser argument. It includes smooth dependence of the pointwise Moser solution and the restricted Cartan identity. Its ambient extension and uniform spatial support make it suitable for integration to a complete ambient flow. No contact or tangency condition is asserted outside the specified time interval and level set.
-- source:
--   Geiges, Contact geometry, Handbook of Differential Geometry II (2006), https://arxiv.org/abs/math/0307242, proof of Theorem 2.20, printed pp. 14–15, equations (2.1)–(2.2). Ambient extension with a cutoff is the compact regular-level formulation of the smooth vector-field construction; the Lie equation uses Cartan's formula and α_t(X_t)=0 on M.

import Definitions.Def_GrayStability_Basic

open scoped ContDiff
open GrayStability

theorem GrayStability.smooth_moser_lie_generator {n c : ℕ}
    (F : E n → (Fin c → ℝ)) (hF : IsCompactRegularLevel F)
    (α : ℝ → OneForm n) (hα : IsContactFamilyOn F α) :
    ∃ X : ℝ → E n → E n, ∃ μ : ℝ → E n → ℝ,
      ContDiff ℝ ∞ (fun p : ℝ × E n => X p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E n => μ p.1 p.2) ∧
      (∃ K : Set (E n), IsCompact K ∧ ∀ t y, y ∉ K → X t y = 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ levelSet F,
        X t y ∈ contactPlane F (α t) y) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ levelSet F, ∀ v ∈ tangentSpace F y,
        formTimeDeriv α t y v + lieDerivOneForm (X t) (α t) y v =
          μ t y * α t y v := by sorry
