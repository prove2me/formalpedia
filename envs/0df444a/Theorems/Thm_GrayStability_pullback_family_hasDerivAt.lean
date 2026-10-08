-- Prove2me | Theorems.Thm_GrayStability_pullback_family_hasDerivAt
-- name    : GrayStability.pullback_family_hasDerivAt
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-05T20:27:33.263984+00:00
-- url     : https://prove2.me/theorems/59801e86-5162-4d97-8b0c-68d1e905ef3b
-- title:
--   Lemma 2.19: derivative of a pulled-back family of forms along a flow
-- statement:
--   Let $\eta_t$ be a smooth family of one-forms on $\mathbb{R}^n$ and $X_t$ a smooth time-dependent vector field. Let $\psi_t$ be a smooth family of bijections of $\mathbb{R}^n$ with $\psi_0=\mathrm{id}$ that is the flow of $X_t$: $\partial_t\psi_t(y)=X_t(\psi_t(y))$. Then for all $t$, $y$ and $v$,
--   $$\frac{d}{dt}\big(\psi_t^*\eta_t\big)_y(v)=\big(\psi_t^*(\dot\eta_t+\mathcal{L}_{X_t}\eta_t)\big)_y(v),$$
--   where $(\psi^*\eta)_y(v)=\eta_{\psi(y)}(D\psi(y)v)$ and $(\mathcal{L}_X\eta)_y(v)=D\eta_y(X(y))(v)+\eta_y(DX(y)v)$.
--
--   This is the identity that turns the equation $\psi_t^*\alpha_t=\lambda_t\alpha_0$ of Gray's theorem into an equation for the vector field $X_t$ (the Moser trick).
-- source:
--   Geiges, Contact geometry, Handbook of Differential Geometry Vol. II (2006) 315-382, https://arxiv.org/abs/math/0307242, Lemma 2.19, p. 13 (stated for $k$-forms on a manifold; here $k=1$ on $\mathbb{R}^n$)

import Definitions.Def_GrayStability_Basic

open scoped ContDiff

namespace GrayStability

/-- Geiges, Lemma 2.19 (one-forms on `ℝⁿ`): if `ψ_t` is an isotopy that is the flow of
the time-dependent vector field `X_t`, then
`d/dt (ψ_t^* η_t) = ψ_t^* (η̇_t + L_{X_t} η_t)`. -/
theorem pullback_family_hasDerivAt {n : ℕ} (η : ℝ → OneForm n) (hη : IsSmoothFamily η)
    (X : ℝ → E n → E n) (hX : ContDiff ℝ ∞ (fun p : ℝ × E n => X p.1 p.2))
    (ψ : ℝ → E n → E n) (hψ : ContDiff ℝ ∞ (fun p : ℝ × E n => ψ p.1 p.2))
    (h0 : ∀ y, ψ 0 y = y) (hbij : ∀ t, Function.Bijective (ψ t))
    (hflow : ∀ t y, HasDerivAt (fun s => ψ s y) (X t (ψ t y)) t)
    (t : ℝ) (y v : E n) :
    HasDerivAt (fun s => pullback (ψ s) (η s) y v)
      (formTimeDeriv η t (ψ t y) (fderiv ℝ (ψ t) y v) +
        lieDerivOneForm (X t) (η t) (ψ t y) (fderiv ℝ (ψ t) y v)) t := by sorry

end GrayStability
