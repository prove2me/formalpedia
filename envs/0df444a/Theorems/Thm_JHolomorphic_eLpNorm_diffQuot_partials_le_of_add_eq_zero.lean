-- Prove2me | Theorems.Thm_JHolomorphic_eLpNorm_diffQuot_partials_le_of_add_eq_zero
-- name    : JHolomorphic.eLpNorm_diffQuot_partials_le_of_add_eq_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-14T20:24:24.184233+00:00
-- url     : https://prove2.me/theorems/cc1258c9-2b56-4650-ad5a-56362351a820
-- title:
--   Uniform $L^p$ bound on difference quotients of the weak partials of a weakly $J$-holomorphic map
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $p>2$, $U\subseteq\mathbb C$ open, $J:E\to\mathrm{End}(E)$, and $u:U\to E$ continuous with weak partials $u_s,u_t$ and $u_s+J(u)u_t=0$ a.e. on $U$. Fix $z_0$, $0<r$, $3r\le R_0$ with $\overline B(z_0,R_0)\subseteq U$ and $u,u_s,u_t\in L^p(\overline B(z_0,R_0))$. Fix $J_0\in\mathrm{End}(E)$ and constants $C_f,C_M,L,\varepsilon\ge0$ such that:
--
--   - $\|\xi_s\|_{L^p(V)}+\|\xi_t\|_{L^p(V)}\le C_f\|\xi_s+J_0\xi_t\|_{L^p(V)}$ for every open $V$ and every continuous compactly supported $\xi$ with $\operatorname{supp}\xi\subseteq V$ and weak partials in $L^p(V)$;
--   - $\sup|\xi|\le C_M(\|\xi_s\|_{L^p}+\|\xi_t\|_{L^p})$ on $B(z_0,2r)$ for continuous $\xi$ supported in $B(z_0,2r)$ with weak partials in $L^p(B(z_0,2r))$;
--   - $\|J(u(z))-J_0\|\le\varepsilon$ and $\|J(u(z))-J(u(z'))\|\le L|u(z)-u(z')|$ for $z,z'\in\overline B(z_0,R_0)$;
--   - $C_f\varepsilon\le\frac14$ and $C_fLC_M\|u_t\|_{L^p(\overline B(z_0,R_0))}\le\frac14$.
--
--   Let $\beta\in C^\infty(\mathbb C,\mathbb R)$ with $|\beta|\le1$, $\beta=1$ on $B(z_0,r)$, $\operatorname{supp}\beta\subseteq\overline B(z_0,3r/2)$ and $\|D\beta\|\le M$. Then for every unit vector $v\in\mathbb C$ and every real $h\ne0$ with $|h|<r$,
--   $$\Big\|\tfrac{u_s(\cdot+hv)-u_s}{h}\Big\|_{L^p(B(z_0,r))}+\Big\|\tfrac{u_t(\cdot+hv)-u_t}{h}\Big\|_{L^p(B(z_0,r))}\le2C_fM(1+\|J_0\|+\varepsilon)\,\big\|(\operatorname{Re}v)u_s+(\operatorname{Im}v)u_t\big\|_{L^p(\overline B(z_0,R_0))}.$$
--
--   This is the uniform difference-quotient estimate that, together with the published `JHolomorphic.exists_hasWeakPartialsOn_of_diffQuot_bounded` (5692a44b), yields second weak derivatives of weakly $J$-holomorphic maps in $L^p$.
--
--   Formalization Note: norms are `eLpNorm … (ENNReal.ofReal p)` with `volume.restrict`; the right-hand side is an `ENNReal.ofReal` of a real number; `HasWeakPartialsOn` is the platform definition.
-- source:
--   Standard elliptic regularity (cf. McDuff–Salamon, J-holomorphic curves, App. B.4)

import Definitions.Def_JHolomorphic_Setting

namespace JHolomorphic

open MeasureTheory Metric
open scoped ContDiff

/-- Let `p > 2`, `U ⊆ ℂ` open and `u` continuous on `U` with weak partials `us`, `ut` and
`us + J(u) ut = 0` almost everywhere on `U`. Let `closedBall z₀ R₀ ⊆ U`, `0 < r`, `3 r ≤ R₀`, with
`u, us, ut ∈ L^p(closedBall z₀ R₀)`. Assume, for a fixed `J₀` and constants `Cf, CM, L, ε ≥ 0`:
* the `L^p` estimate `‖ξs‖ + ‖ξt‖ ≤ Cf ‖ξs + J₀ ξt‖` for compactly supported continuous `ξ` with
  `L^p` weak partials on any open set;
* the sup bound `‖ξ‖∞ ≤ CM (‖ξs‖ + ‖ξt‖)` for continuous `ξ` supported in `ball z₀ (2 r)`;
* `‖J(u z) - J₀‖ ≤ ε` and `‖J(u z) - J(u z')‖ ≤ L ‖u z - u z'‖` on `closedBall z₀ R₀`;
* `Cf ε ≤ 1/4` and `Cf L CM ‖ut‖_{L^p(closedBall z₀ R₀)} ≤ 1/4`.
Let `β` be a smooth real function with `‖β‖ ≤ 1`, `β = 1` on `ball z₀ r`, support in
`closedBall z₀ (3 r / 2)` and `‖Dβ‖ ≤ M`. Then for every unit vector `v` and real `h ≠ 0` with
`|h| < r`, the difference quotients `h⁻¹ (us(· + h v) - us)` and `h⁻¹ (ut(· + h v) - ut)` have
`L^p(ball z₀ r)` norms summing to at most
`2 Cf M (1 + ‖J₀‖ + ε) ‖(Re v) us + (Im v) ut‖_{L^p(closedBall z₀ R₀)}`. -/
theorem eLpNorm_diffQuot_partials_le_of_add_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p : ℝ) (hp : 2 < p)
    (J : E → E →L[ℝ] E) (U : Set ℂ) (hU : IsOpen U)
    (u us ut : ℂ → E) (hu : ContinuousOn u U)
    (hw : HasWeakPartialsOn U u us ut)
    (heq : ∀ᵐ z ∂(volume.restrict U), us z + J (u z) (ut z) = 0)
    (z₀ : ℂ) (R₀ r : ℝ) (hr : 0 < r) (h3r : 3 * r ≤ R₀) (hS : closedBall z₀ R₀ ⊆ U)
    (hLpS : MemLp u (ENNReal.ofReal p) (volume.restrict (closedBall z₀ R₀)) ∧
      MemLp us (ENNReal.ofReal p) (volume.restrict (closedBall z₀ R₀)) ∧
      MemLp ut (ENNReal.ofReal p) (volume.restrict (closedBall z₀ R₀)))
    (J₀ : E →L[ℝ] E) (Cf CM L ε : ℝ) (hCf0 : 0 ≤ Cf) (hCM0 : 0 ≤ CM) (hL0 : 0 ≤ L)
    (hε0 : 0 ≤ ε)
    (hCf : ∀ U : Set ℂ, IsOpen U → ∀ ξ ξs ξt : ℂ → E, Continuous ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ U → HasWeakPartialsOn U ξ ξs ξt →
      MemLp ξs (ENNReal.ofReal p) (volume.restrict U) →
      MemLp ξt (ENNReal.ofReal p) (volume.restrict U) →
      eLpNorm ξs (ENNReal.ofReal p) (volume.restrict U) +
          eLpNorm ξt (ENNReal.ofReal p) (volume.restrict U) ≤
        ENNReal.ofReal Cf * eLpNorm (fun z => ξs z + J₀ (ξt z)) (ENNReal.ofReal p)
          (volume.restrict U))
    (hCM : ∀ ξ ξs ξt : ℂ → E, Continuous ξ →
      tsupport ξ ⊆ ball z₀ (2 * r) → HasWeakPartialsOn (ball z₀ (2 * r)) ξ ξs ξt →
      MemLp ξs (ENNReal.ofReal p) (volume.restrict (ball z₀ (2 * r))) →
      MemLp ξt (ENNReal.ofReal p) (volume.restrict (ball z₀ (2 * r))) →
      ∀ z, ‖ξ z‖ₑ ≤ ENNReal.ofReal CM *
        (eLpNorm ξs (ENNReal.ofReal p) (volume.restrict (ball z₀ (2 * r))) +
          eLpNorm ξt (ENNReal.ofReal p) (volume.restrict (ball z₀ (2 * r)))))
    (hJε : ∀ z ∈ closedBall z₀ R₀, ‖J (u z) - J₀‖ ≤ ε)
    (hJL : ∀ z ∈ closedBall z₀ R₀, ∀ z' ∈ closedBall z₀ R₀,
      ‖J (u z) - J (u z')‖ ≤ L * ‖u z - u z'‖)
    (hsm1 : Cf * ε ≤ 1 / 4)
    (hsm2 : Cf * L * CM *
      (eLpNorm ut (ENNReal.ofReal p) (volume.restrict (closedBall z₀ R₀))).toReal ≤ 1 / 4)
    (β : ℂ → ℝ) (hβ : ContDiff ℝ ∞ β) (hβs : tsupport β ⊆ closedBall z₀ (3 * r / 2))
    (hβ1 : ∀ z ∈ ball z₀ r, β z = 1) (hβb : ∀ z, ‖β z‖ ≤ 1)
    (M : ℝ) (hM : ∀ z, ‖fderiv ℝ β z‖ ≤ M)
    (v : ℂ) (hv : ‖v‖ = 1) (h : ℝ) (hh0 : h ≠ 0) (hhr : |h| < r) :
    eLpNorm (fun z => h⁻¹ • (us (z + (h : ℂ) * v) - us z)) (ENNReal.ofReal p)
        (volume.restrict (ball z₀ r)) +
      eLpNorm (fun z => h⁻¹ • (ut (z + (h : ℂ) * v) - ut z)) (ENNReal.ofReal p)
        (volume.restrict (ball z₀ r)) ≤
    ENNReal.ofReal (2 * (Cf * (M * (1 + ‖J₀‖ + ε)) *
      (eLpNorm (fun z => v.re • us z + v.im • ut z) (ENNReal.ofReal p)
        (volume.restrict (closedBall z₀ R₀))).toReal)) := by
  sorry

end JHolomorphic
