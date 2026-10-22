-- Prove2me | Theorems.Thm_JHolomorphic_eLpNorm_fderiv_fderiv_ball_le
-- name    : JHolomorphic.eLpNorm_fderiv_fderiv_ball_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-22T00:29:01.887167+00:00
-- url     : https://prove2.me/theorems/983a0b57-05b3-49b9-a083-5459352eb81f
-- title:
--   An interior $L^p$ bound for second derivatives of solutions of the linearized Cauchy–Riemann equation on a half disc
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $p>2$, $U\subseteq\mathbb C$ open, $u:\mathbb C\to E$ $C^\infty$ on $U$, $J_c:E\to\mathrm{End}(E)$ and $J_0\in\mathrm{End}(E)$. Assume:
--   - $C_F\ge0$ and $\|\partial_sg\|_p+\|\partial_tg\|_p\le C_F\|\partial_sg+J_0\partial_tg\|_p$ for every compactly supported $C^1$ map $g:\mathbb C\to E$;
--   - $C_K\ge0$ and $\sup|g|\le C_K\rho^{1-2/p}(\|\partial_sg\|_p+\|\partial_tg\|_p)$ for every $C^1$ map $g$ with support in a disc of radius $\rho$;
--   - for every direction $e$, $\xi=Du(\cdot)e$ satisfies $\partial_s\xi+J_c(u)\partial_t\xi+DJ_c(u)[\xi]\,\partial_tu=0$ on $U$;
--   - $B(z_0,r)\subseteq U$, $\beta$ is a smooth real function with support in $B(z_0,r)$ and $\|D\beta\|\le B_\beta$;
--   - on $B(z_0,r)$: $\|J_0-J_c(u)\|\le\eta$, $\|DJ_c(u)\|\le\Lambda$; moreover $\|J_0\|\le A$ and $\|Du\|_{L^p(B(z_0,r))}\le M$ ($\eta,\Lambda,M\ge0$);
--   - $C_F\eta\le\frac14$ and $C_F\Lambda C_Kr^{1-2/p}M\le\frac14$.
--   - $\beta=1$ on $B(z_0,r/2)$.
--
--   Then
--   $$\|D^2u\|_{L^p(B(z_0,r/2))}\le 4C_F\,B_\beta(1+A+\eta)\,M .$$
--   This is the local form of the interior $W^{2,p}$ estimate for pseudoholomorphic maps, with explicit dependence of the constant.
--
--   **Formalization Note** The two estimates are passed as hypotheses `hF`, `hK` with constants `ENNReal.ofReal CF`, `ENNReal.ofReal (CK * r ^ (1 - 2 / p))`. The equation is `heq : ∀ e : ℂ, ∀ z ∈ U, fderiv ℝ (fun y => fderiv ℝ u y e) z 1 + (Jc (u z) (fderiv ℝ (fun y => fderiv ℝ u y e) z Complex.I) + fderiv ℝ Jc (u z) (fderiv ℝ u z e) (fderiv ℝ u z Complex.I)) = 0`, and `hβ1 : ∀ z ∈ ball z₀ (r / 2), β z = 1`. The conclusion is `eLpNorm (fderiv ℝ (fderiv ℝ u)) (ENNReal.ofReal p) (volume.restrict (ball z₀ (r / 2))) ≤ ENNReal.ofReal (4 * (CF * (Bβ * (1 + A + η) * M)))`, in operator norm.
-- source:
--   Interior L^p estimates for pseudoholomorphic maps; D. McDuff, D. Salamon, J-holomorphic Curves and Symplectic Topology, §B.4; used for C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lecture 2, Theorem 2.22

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal NNReal

/-- Interior `L^p` bound for the second derivative of a smooth solution `u` of the differentiated
nonlinear Cauchy–Riemann equation `∂ₛξ + J_c(u) ∂ₜξ + DJ_c(u)[ξ] ∂ₜu = 0`, `ξ = Du(·) e`
(all `e`), on the half disc `B(z₀, r/2)`, under the hypotheses of
`eLpNorm_fderiv_smul_fderiv_apply_le` plus `β = 1` on `B(z₀, r/2)`:
`‖D²u‖_{L^p(B(z₀,r/2))} ≤ 4 CF Bβ (1 + A + η) M`. -/
theorem eLpNorm_fderiv_fderiv_ball_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (p : ℝ) (hp : 2 < p) (CF CK : ℝ) (hCF : 0 ≤ CF) (hCK : 0 ≤ CK)
    (J₀ : E →L[ℝ] E)
    (hF : ∀ g : ℂ → E, ContDiff ℝ 1 g → HasCompactSupport g →
      eLpNorm (fun z => fderiv ℝ g z 1) (ENNReal.ofReal p) volume +
          eLpNorm (fun z => fderiv ℝ g z Complex.I) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal CF *
          eLpNorm (fun z => fderiv ℝ g z 1 + J₀ (fderiv ℝ g z Complex.I)) (ENNReal.ofReal p)
            volume)
    (hK : ∀ (c : ℂ) (r : ℝ), 0 < r → ∀ g : ℂ → E, ContDiff ℝ 1 g →
      tsupport g ⊆ ball c r → ∀ z, ‖g z‖ₑ ≤ ENNReal.ofReal (CK * r ^ (1 - 2 / p)) *
        (eLpNorm (fun y => fderiv ℝ g y 1) (ENNReal.ofReal p) volume +
          eLpNorm (fun y => fderiv ℝ g y Complex.I) (ENNReal.ofReal p) volume))
    (U : Set ℂ) (hU : IsOpen U) (u : ℂ → E) (hu : ContDiffOn ℝ ∞ u U)
    (Jc : E → E →L[ℝ] E)
    (heq : ∀ e : ℂ, ∀ z ∈ U, fderiv ℝ (fun y => fderiv ℝ u y e) z 1 +
      (Jc (u z) (fderiv ℝ (fun y => fderiv ℝ u y e) z Complex.I) +
        fderiv ℝ Jc (u z) (fderiv ℝ u z e) (fderiv ℝ u z Complex.I)) = 0)
    (z₀ : ℂ) (r : ℝ) (hr : 0 < r) (hball : ball z₀ r ⊆ U)
    (β : ℂ → ℝ) (hβ : ContDiff ℝ ∞ β) (hβs : tsupport β ⊆ ball z₀ r)
    (hβ1 : ∀ z ∈ ball z₀ (r / 2), β z = 1) (Bβ : ℝ) (hBβ : ∀ z, ‖fderiv ℝ β z‖ ≤ Bβ)
    (η Λ A M : ℝ) (hη0 : 0 ≤ η) (hΛ0 : 0 ≤ Λ) (hM0 : 0 ≤ M)
    (hη : ∀ z ∈ ball z₀ r, ‖J₀ - Jc (u z)‖ ≤ η)
    (hΛ : ∀ z ∈ ball z₀ r, ‖fderiv ℝ Jc (u z)‖ ≤ Λ) (hA : ‖J₀‖ ≤ A)
    (hM : eLpNorm (fderiv ℝ u) (ENNReal.ofReal p) (volume.restrict (ball z₀ r)) ≤
      ENNReal.ofReal M)
    (hs1 : CF * η ≤ 1 / 4) (hs2 : CF * Λ * (CK * r ^ (1 - 2 / p)) * M ≤ 1 / 4) :
    eLpNorm (fderiv ℝ (fderiv ℝ u)) (ENNReal.ofReal p) (volume.restrict (ball z₀ (r / 2))) ≤
      ENNReal.ofReal (4 * (CF * (Bβ * (1 + A + η) * M))) := by
  sorry

end JHolomorphic
