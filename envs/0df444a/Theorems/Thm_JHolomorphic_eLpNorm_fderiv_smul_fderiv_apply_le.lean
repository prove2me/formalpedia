-- Prove2me | Theorems.Thm_JHolomorphic_eLpNorm_fderiv_smul_fderiv_apply_le
-- name    : JHolomorphic.eLpNorm_fderiv_smul_fderiv_apply_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-22T00:25:15.536319+00:00
-- url     : https://prove2.me/theorems/4b423a07-61f9-4c19-8004-dbbed99b05bc
-- title:
--   An $L^p$ bound for a cut-off directional derivative of a solution of the linearized Cauchy–Riemann equation
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $p>2$, $U\subseteq\mathbb C$ open, $u:\mathbb C\to E$ $C^\infty$ on $U$, $J_c:E\to\mathrm{End}(E)$ and $J_0\in\mathrm{End}(E)$. Assume:
--   - $C_F\ge0$ and $\|\partial_sg\|_p+\|\partial_tg\|_p\le C_F\|\partial_sg+J_0\partial_tg\|_p$ for every compactly supported $C^1$ map $g:\mathbb C\to E$;
--   - $C_K\ge0$ and $\sup|g|\le C_K\rho^{1-2/p}(\|\partial_sg\|_p+\|\partial_tg\|_p)$ for every $C^1$ map $g$ with support in a disc of radius $\rho$;
--   - for every direction $e$, $\xi=Du(\cdot)e$ satisfies $\partial_s\xi+J_c(u)\partial_t\xi+DJ_c(u)[\xi]\,\partial_tu=0$ on $U$;
--   - $B(z_0,r)\subseteq U$, $\beta$ is a smooth real function with support in $B(z_0,r)$ and $\|D\beta\|\le B_\beta$;
--   - on $B(z_0,r)$: $\|J_0-J_c(u)\|\le\eta$, $\|DJ_c(u)\|\le\Lambda$; moreover $\|J_0\|\le A$ and $\|Du\|_{L^p(B(z_0,r))}\le M$ ($\eta,\Lambda,M\ge0$);
--   - $C_F\eta\le\frac14$ and $C_F\Lambda C_Kr^{1-2/p}M\le\frac14$.
--
--   Then for every $e\in\mathbb C$ with $|e|\le1$, the map $g=\beta\,Du(\cdot)e$ satisfies
--   $$\|\partial_sg\|_{L^p}+\|\partial_tg\|_{L^p}\le 2C_F\,B_\beta(1+A+\eta)\,M .$$
--   This is the local step of the interior $W^{2,p}$ estimate for pseudoholomorphic maps: the constants depend only on the listed quantities.
--
--   **Formalization Note** The two estimates are passed as hypotheses `hF`, `hK` with constants `ENNReal.ofReal CF`, `ENNReal.ofReal (CK * r ^ (1 - 2 / p))`. The equation is `heq : ∀ z ∈ U, fderiv ℝ (fun y => fderiv ℝ u y e) z 1 + (Jc (u z) (fderiv ℝ (fun y => fderiv ℝ u y e) z Complex.I) + fderiv ℝ Jc (u z) (fderiv ℝ u z e) (fderiv ℝ u z Complex.I)) = 0`. The norms are `eLpNorm … (ENNReal.ofReal p) volume`, and the bound is `ENNReal.ofReal (2 * (CF * (Bβ * (1 + A + η) * M)))`.
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

/-- Interior `L^p` estimate for the cut-off directional derivative `β · Du(·) e` (`‖e‖ ≤ 1`) of a
smooth solution `u` of the differentiated nonlinear Cauchy–Riemann equation
`∂ₛξ + J_c(u) ∂ₜξ + DJ_c(u)[ξ] ∂ₜu = 0`, `ξ = Du(·) e`, on a disc `B(z₀, r) ⊆ U`.
Here `CF` is a constant of the `L^p` estimate for `∂ₛ + J₀ ∂ₜ`, `CK` a constant of the sup bound
`‖g‖_∞ ≤ CK r^{1-2/p} (‖∂ₛg‖_p + ‖∂ₜg‖_p)` for `C¹` maps supported in a disc of radius `r`, `β` is
a smooth cutoff supported in the disc with `‖Dβ‖ ≤ Bβ`, `‖J₀ - J_c(u)‖ ≤ η` and `‖DJ_c(u)‖ ≤ Λ` on
the disc, `‖J₀‖ ≤ A`, and `‖Du‖_{L^p(B(z₀,r))} ≤ M`. If `CF η ≤ 1/4` and
`CF Λ CK r^{1-2/p} M ≤ 1/4`, then the `L^p` norms of `∂ₛ(βξ)` and `∂ₜ(βξ)` add up to at most
`2 CF Bβ (1 + A + η) M`. -/
theorem eLpNorm_fderiv_smul_fderiv_apply_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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
    (Jc : E → E →L[ℝ] E) (e : ℂ) (he : ‖e‖ ≤ 1)
    (heq : ∀ z ∈ U, fderiv ℝ (fun y => fderiv ℝ u y e) z 1 +
      (Jc (u z) (fderiv ℝ (fun y => fderiv ℝ u y e) z Complex.I) +
        fderiv ℝ Jc (u z) (fderiv ℝ u z e) (fderiv ℝ u z Complex.I)) = 0)
    (z₀ : ℂ) (r : ℝ) (hr : 0 < r) (hball : ball z₀ r ⊆ U)
    (β : ℂ → ℝ) (hβ : ContDiff ℝ ∞ β) (hβs : tsupport β ⊆ ball z₀ r)
    (Bβ : ℝ) (hBβ : ∀ z, ‖fderiv ℝ β z‖ ≤ Bβ)
    (η Λ A M : ℝ) (hη0 : 0 ≤ η) (hΛ0 : 0 ≤ Λ) (hM0 : 0 ≤ M)
    (hη : ∀ z ∈ ball z₀ r, ‖J₀ - Jc (u z)‖ ≤ η)
    (hΛ : ∀ z ∈ ball z₀ r, ‖fderiv ℝ Jc (u z)‖ ≤ Λ) (hA : ‖J₀‖ ≤ A)
    (hM : eLpNorm (fderiv ℝ u) (ENNReal.ofReal p) (volume.restrict (ball z₀ r)) ≤
      ENNReal.ofReal M)
    (hs1 : CF * η ≤ 1 / 4) (hs2 : CF * Λ * (CK * r ^ (1 - 2 / p)) * M ≤ 1 / 4) :
    eLpNorm (fun z => fderiv ℝ (fun y => β y • fderiv ℝ u y e) z 1) (ENNReal.ofReal p) volume +
        eLpNorm (fun z => fderiv ℝ (fun y => β y • fderiv ℝ u y e) z Complex.I)
          (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (2 * (CF * (Bβ * (1 + A + η) * M))) := by
  sorry

end JHolomorphic
