-- Prove2me | Theorems.Thm_ModularCurve_exists_invariant_localModel_tendsto_integral_dbarLogDeriv_smoothedFundamental_periodAlongOf
-- name    : ModularCurve.exists_invariant_localModel_tendsto_integral_dbarLogDeriv_smoothedFundamental_periodAlongOf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/de2dbf23-c70a-5d8b-9e80-35ee0f833c84
-- title:
--   Invariant function with prescribed divisor pairing to Abel–Jacobi sums
-- statement:
--   Let $\Gamma\le SL(2,\mathbb Z)$ be a subgroup of finite index containing $-1$, let $S$ be a finite subset of the upper half plane $\mathfrak H$ and let $n:\mathfrak H\to\mathbb Z$ satisfy: $n$ is $\Gamma$-invariant ($n(\gamma\tau)=n(\tau)$); every $\tau$ with $n(\tau)\ne 0$ is $\Gamma$-equivalent to some point of $S$; distinct points of $S$ are $\Gamma$-inequivalent; $\#\mathrm{Stab}_\Gamma(s)\mid 2n(s)$ for $s\in S$; and $\sum_{s\in S}n(s)/\#\mathrm{Stab}_\Gamma(s)=0$ in $\mathbb C$. Let $h:\mathbb R\to\mathbb C\to\mathbb C$ be given by $h(T,z)=\mathrm{smoothedFundamental}\,\Gamma\,T\,z$, the finite sum over cosets $q\in SL(2,\mathbb Z)/\Gamma$ of the cut-off $\mathrm{puCut}\,T$ evaluated at the Möbius image of $z$ under a representative of $q$, viewed as a complex number. Then there is $V:\mathbb C\to\mathbb C$ with: (i) $V(\gamma\tau)=V(\tau)$ for all $\gamma\in\Gamma$, $\tau\in\mathfrak H$; (ii) for each $\tau\in\mathfrak H$ one has $V(z)=(z-\tau)^{n(\tau)}\Psi(z)$ near $\tau$ for some $\Psi$ which is $C^1$ in the real sense at $\tau$ with $\Psi(\tau)\ne 0$; (iii) for each $\sigma\in SL(2,\mathbb Z)$ there is $Y\in\mathbb R$ with $V(\sigma z)=1$ whenever $\operatorname{Im}z>Y$; (iv) for every $T\in\mathbb R$ and every weight-two cusp form $g$ on $\Gamma$ the function $z\mapsto g(z)\,h(T,z)\,\bar\partial V(z)/V(z)$, with $\bar\partial V=\tfrac12(\partial_xV+i\,\partial_yV)$ expressed through the real Fréchet derivative of $V$ in the directions $1$ and $i$, is integrable on $\mathbb C$; and (v) for every such $g$, $$\frac{2}{\pi}\int_{\mathbb C}g\,h(T,\cdot)\,\frac{\bar\partial V}{V}\;\longrightarrow\;\sum_{s\in S}\frac{2n(s)}{\#\mathrm{Stab}_\Gamma(s)}\int_0^1 g\bigl(\mathrm{segmentPath}\,i\,s\,t\bigr)(s-i)\,dt$$ as $T\to\infty$, the right-hand integrals being the periods of $g$ along the segments from $i$ to $s$.
--
--   This supplies the analytic input to the Abel–Jacobi argument for modular curves: a $\Gamma$-invariant function on the upper half plane with prescribed degree-zero divisor (the multiplicity $n(\tau)$ at $\tau$), trivial near every cusp, whose $\bar\partial$-logarithmic derivative pairs against weight-two cusp forms, in the limit of the smoothed fundamental domain cut-offs, to the sum of periods $\sum_s \frac{2n(s)}{\#\mathrm{Stab}_\Gamma(s)}\int_i^s g$. It is used by [`ModularCurve.exists_mem_periodLatticeOf_tendsto_windingPairing_smoothedFundamental`](thm.html#ModularCurve.exists_mem_periodLatticeOf_tendsto_windingPairing_smoothedFundamental) to show that such Abel–Jacobi sums lie in the period lattice.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_invariant_localModel_tendsto_integral_dbarLogDeriv_smoothedFundamental_periodAlongOf.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_ModularCurve_SmoothedFundamental

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open UpperHalfPlane MeasureTheory Filter
open scoped MatrixGroups Topology

theorem ModularCurve.exists_invariant_localModel_tendsto_integral_dbarLogDeriv_smoothedFundamental_periodAlongOf
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ)
    (S : Finset ℍ) (n : ℍ → ℤ)
    (hn : ∀ (γ : Γ) (τ : ℍ), n ((γ : SL(2, ℤ)) • τ) = n τ)
    (hcov : ∀ τ : ℍ, n τ ≠ 0 → ∃ s ∈ S, ∃ γ : Γ, (γ : SL(2, ℤ)) • s = τ)
    (hinj : ∀ s ∈ S, ∀ t ∈ S,
      (∃ γ : Γ, (γ : SL(2, ℤ)) • s = t) → s = t)
    (hdvd : ∀ s ∈ S, (Nat.card (MulAction.stabilizer Γ s) : ℤ) ∣ 2 * n s)
    (hdeg : ∑ s ∈ S, (n s : ℂ) /
      (Nat.card (MulAction.stabilizer Γ s) : ℂ) = 0)
    (h : ℝ → ℂ → ℂ)
    (hh : ∀ T z, h T z = (ModularCurve.smoothedFundamental Γ T z : ℂ)) :
    ∃ V : ℂ → ℂ,
      (∀ (γ : Γ) (τ : ℍ), V (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) = V τ) ∧
      (∀ τ : ℍ, ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ (τ : ℂ) ∧ Ψ τ ≠ 0 ∧
        V =ᶠ[𝓝 (τ : ℂ)] fun z => (z - τ) ^ (n τ) * Ψ z) ∧
      (∀ σ : SL(2, ℤ), ∃ Y : ℝ, ∀ z : ℂ, Y < z.im → V ((σ • ofComplex z : ℍ) : ℂ) = 1) ∧
      (∀ (T : ℝ) (g : CuspForm Γ 2),
        Integrable fun z : ℂ => g (ofComplex z) * h T z *
          ((fderiv ℝ V z 1 + Complex.I * fderiv ℝ V z Complex.I) / 2 / V z)) ∧
      ∀ g : CuspForm Γ 2,
        Tendsto (fun T : ℝ => 2 / Real.pi * ∫ z : ℂ, g (ofComplex z) * h T z *
            ((fderiv ℝ V z 1 + Complex.I * fderiv ℝ V z Complex.I) / 2 / V z)) atTop
          (𝓝 (∑ s ∈ S, 2 * (n s : ℂ) /
            (Nat.card (MulAction.stabilizer Γ s) : ℂ) *
              ModularCurve.periodAlongOf Γ UpperHalfPlane.I s g)) := by sorry
