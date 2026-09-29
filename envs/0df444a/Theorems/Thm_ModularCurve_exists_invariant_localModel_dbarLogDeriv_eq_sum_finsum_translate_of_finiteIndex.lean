-- Prove2me | Theorems.Thm_ModularCurve_exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate_of_finiteIndex
-- name    : ModularCurve.exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate_of_finiteIndex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/96fe7055-d1e7-503c-9bfc-09a894b990cf
-- title:
--   Γ-invariant function with prescribed divisor and periodised partial̄-kernel
-- statement:
--   Let $\Gamma\le\mathrm{SL}_2(\mathbb Z)$ be a subgroup of finite index containing $-1$, let $S$ be a finite set of points of the upper half-plane $\mathfrak H$, and let $n:\mathfrak H\to\mathbb Z$ satisfy: $n(\gamma\cdot\tau)=n(\tau)$ for all $\gamma\in\Gamma$ and $\tau\in\mathfrak H$; every $\tau$ with $n(\tau)\ne 0$ lies in the $\Gamma$-orbit of some $s\in S$; any two points of $S$ in the same $\Gamma$-orbit coincide; $\#\mathrm{Stab}_\Gamma(s)\mid 2n(s)$ in $\mathbb Z$ for $s\in S$; and $\sum_{s\in S}n(s)/\#\mathrm{Stab}_\Gamma(s)=0$ in $\mathbb C$. Then there are $V:\mathbb C\to\mathbb C$, a point $b\in\mathfrak H$, $m:\mathfrak H\to\mathbb Z$ and $F:\mathfrak H\to(\mathbb C\to\mathbb C)$ such that: (i) $V(\gamma\cdot\tau)=V(\tau)$ for $\gamma\in\Gamma$, $\tau\in\mathfrak H$; (ii) for each $\tau\in\mathfrak H$ there is $\Psi$, real-$C^1$ at $\tau$ with $\Psi(\tau)\ne0$, with $V(z)=(z-\tau)^{n(\tau)}\Psi(z)$ near $\tau$; (iii) for each $\sigma\in\mathrm{SL}_2(\mathbb Z)$ there is $Y\in\mathbb R$ with $V(\sigma\cdot z)=1$ whenever $\operatorname{Im}z>Y$; (iv) for $s\in S$, $F_s$ is continuous with compact support whose closure lies in $\mathfrak H$, and for all $E,E':\mathbb C\to\mathbb C$ with $E$ having derivative $E'(z)$ at every $z$ of positive imaginary part, $E'F_s$ is integrable and $\int_{\mathbb C}E'F_s=\pi\,(E(s)-E(b))$; (v) $\#\mathrm{Stab}_\Gamma(s)\cdot m(s)=2n(s)$ for $s\in S$; (vi) for almost every $z$ with $\operatorname{Im}z>0$, $$\frac{\tfrac12\bigl(\partial_xV(z)+i\,\partial_yV(z)\bigr)}{V(z)}=\sum_{s\in S}\frac{m(s)}{2}\;\sum_{\gamma\in\Gamma}^{\mathrm{f}}F_s(\gamma\cdot z)\,\overline{\bigl(\mathrm{denom}(\gamma,z)^{-2}\bigr)},$$ the inner sum being a finsum over $\Gamma$ and $\mathrm{denom}(\gamma,z)=cz+d$.
--
--   This supplies the structural half of the divisor contribution to the winding pairing on the modular curve $X_\Gamma$: a $\Gamma$-invariant smooth function with prescribed degree-zero divisor (the orbit divisor of $n$), identically $1$ near every cusp, whose logarithmic $\bar\partial$-derivative is the $\Gamma$-periodisation, with weight $-2$ automorphy factor, of compactly supported dipole kernels. It is obtained from the local dipole models of [`UpperHalfPlane.exists_localModel_pair_integral_mul_dbarLogDeriv_eq`](thm.html#UpperHalfPlane.exists_localModel_pair_integral_mul_dbarLogDeriv_eq) and is used by [`ModularCurve.exists_invariant_localModel_tendsto_integral_dbarLogDeriv_smoothedFundamental_periodAlongOf`](thm.html#ModularCurve.exists_invariant_localModel_tendsto_integral_dbarLogDeriv_smoothedFundamental_periodAlongOf), where the periodised kernels are unfolded against a smoothed fundamental function.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate_of_finiteIndex.lean

import Mathlib
import Definitions.Def_ModularCurve_SmoothedFundamental

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open UpperHalfPlane MeasureTheory Filter
open scoped MatrixGroups Topology ComplexConjugate

theorem ModularCurve.exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate_of_finiteIndex
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ)
    (S : Finset ℍ) (n : ℍ → ℤ)
    (hn : ∀ (γ : Γ) (τ : ℍ), n ((γ : SL(2, ℤ)) • τ) = n τ)
    (hcov : ∀ τ : ℍ, n τ ≠ 0 → ∃ s ∈ S, ∃ γ : Γ, (γ : SL(2, ℤ)) • s = τ)
    (hinj : ∀ s ∈ S, ∀ t ∈ S,
      (∃ γ : Γ, (γ : SL(2, ℤ)) • s = t) → s = t)
    (hdvd : ∀ s ∈ S, (Nat.card (MulAction.stabilizer Γ s) : ℤ) ∣ 2 * n s)
    (hdeg : ∑ s ∈ S, (n s : ℂ) /
      (Nat.card (MulAction.stabilizer Γ s) : ℂ) = 0) :
    ∃ (V : ℂ → ℂ) (b : ℍ) (m : ℍ → ℤ) (F : ℍ → ℂ → ℂ),
      (∀ (γ : Γ) (τ : ℍ), V (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) = V τ) ∧
      (∀ τ : ℍ, ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ (τ : ℂ) ∧ Ψ τ ≠ 0 ∧
        V =ᶠ[𝓝 (τ : ℂ)] fun z => (z - τ) ^ (n τ) * Ψ z) ∧
      (∀ σ : SL(2, ℤ), ∃ Y : ℝ, ∀ z : ℂ, Y < z.im → V ((σ • ofComplex z : ℍ) : ℂ) = 1) ∧
      (∀ s ∈ S, Continuous (F s) ∧ HasCompactSupport (F s) ∧ tsupport (F s) ⊆ {z : ℂ | 0 < z.im} ∧
        ∀ E E' : ℂ → ℂ, (∀ z : ℂ, 0 < z.im → HasDerivAt E (E' z) z) →
          Integrable (fun z : ℂ => E' z * F s z) ∧
            ∫ z : ℂ, E' z * F s z = Real.pi * (E s - E b)) ∧
      (∀ s ∈ S, (Nat.card (MulAction.stabilizer Γ s) : ℤ) * m s =
        2 * n s) ∧
      ∀ᵐ z : ℂ, 0 < z.im →
        (fderiv ℝ V z 1 + Complex.I * fderiv ℝ V z Complex.I) / 2 / V z =
          ∑ s ∈ S, (m s : ℂ) / 2 * ∑ᶠ γ : Γ,
            F s (((γ : SL(2, ℤ)) • ofComplex z : ℍ) : ℂ) *
              conj (1 / denom ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) (ofComplex z) ^ 2) := by sorry
