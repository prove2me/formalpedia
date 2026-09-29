-- Prove2me | Theorems.Thm_IsRegularLocalRing_exists_ringEquiv_mvPowerSeries_quotient_drinfeldForm_of_eq_mul
-- name    : IsRegularLocalRing.exists_ringEquiv_mvPowerSeries_quotient_drinfeldForm_of_eq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/1897c8c8-c001-5a4b-bbfc-c9056bc810e9
-- title:
--   Drinfeld chart shape for a regular two-dimensional complete local ring
-- statement:
--   Let $q$ be a prime. Let $R$ be a Noetherian local commutative ring, complete with respect to its maximal ideal, which is a regular local ring of Krull dimension $2$, and let $x_0,x_1\in R$ be such that $\mathfrak m_R=(x_0,x_1)$. Let $W$ be a complete discrete valuation ring (a domain, complete for its maximal ideal) with uniformiser $\pi$, so $\mathfrak m_W=(\pi)$, and let $g\colon W\to R$ be a local ring homomorphism which is residually surjective, in the sense that every $r\in R$ satisfies $r-g(w)\in\mathfrak m_R$ for some $w\in W$. Assume finally that $g(\pi)=u_F\,F$ for some $F\in R$ and some unit $u_F\in R$, and that $F\equiv x_0x_1^{q}-x_0^{q}x_1 \pmod{\mathfrak m_R^{\,q+2}}$. The assertion is that there are power series $f,u,v\in W[\![X_0,X_1]\!]$ with $u$ and $v$ units, with $f-(X_0X_1^{q}-X_0^{q}X_1)\in (X_0,X_1)^{q+2}$ (the subtracted series being [`DrinfeldCurve.LocalChart.drinfeldForm q W`](def/DrinfeldCurve_LocalChart.html#L18)), and a ring isomorphism $e\colon R\xrightarrow{\ \sim\ } W[\![X_0,X_1]\!]/(\,\pi v-fu\,)$ such that $e(g(w))$ is the class of the constant series $w$ for every $w\in W$, and $e(x_0)$, $e(x_1)$ are the classes of $X_0$, $X_1$. The unit $v$ is part of the asserted shape of the defining relation rather than an extra constraint.
--
--   This is the local-chart normalisation used for the supersingular deformation ring with Drinfeld level structure (Katz–Mazur 13.8 shape): a regular two-dimensional complete local $W$-algebra in which $\pi$ factors as a unit times $F$ is presented as $W[\![X_0,X_1]\!]$ modulo a single relation whose non-constant part agrees with $X_0X_1^{q}-X_0^{q}X_1$ to order $q+2$. It feeds the statements about Drinfeld-basis-adic rings that produce such a presentation for regular local rings and deduce reducedness of the associated quotient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsRegularLocalRing_exists_ringEquiv_mvPowerSeries_quotient_drinfeldForm_of_eq_mul.lean

import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing FormalGroup

theorem IsRegularLocalRing.exists_ringEquiv_mvPowerSeries_quotient_drinfeldForm_of_eq_mul
    (q : ℕ) [Fact q.Prime]
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    (hreg : IsRegularLocalRing R) (hdim : ringKrullDim R = 2)
    (x₀ x₁ : R) (hmax : maximalIdeal R = Ideal.span {x₀, x₁})
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : maximalIdeal W = Ideal.span {π})
    (g : W →+* R) [IsLocalHom g] (hres : ∀ r : R, ∃ w : W, r - g w ∈ maximalIdeal R)
    (F uF : R) (huF : IsUnit uF) (hπF : g π = uF * F)
    (hF : F - (x₀ * x₁ ^ q - x₀ ^ q * x₁) ∈ maximalIdeal R ^ (q + 2)) :
    ∃ (f u v : MvPowerSeries (Fin 2) W) (_ : IsUnit u) (_ : IsUnit v)
      (_ : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
        (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
      (e : R ≃+* MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C π * v - f * u}),
      (∀ w : W, e (g w) = Ideal.Quotient.mk _ (MvPowerSeries.C w)) ∧
      e x₀ = Ideal.Quotient.mk _ (MvPowerSeries.X 0) ∧ e x₁ = Ideal.Quotient.mk _ (MvPowerSeries.X 1) := by sorry
