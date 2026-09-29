-- Prove2me | Theorems.Thm_ModularCurve_exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate
-- name    : ModularCurve.exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/35df9dba-184a-59f7-98f4-9eccc1879d2a
-- title:
--   Invariant function with prescribed degree-zero Γ₀(N)-invariant divisor
-- statement:
--   Fix $N\ge 1$, a finite set $S\subset\mathfrak H$ and a function $n:\mathfrak H\to\mathbb Z$ subject to: $n$ is invariant under the action of $\Gamma_0(N)$ on $\mathfrak H$ by fractional linear maps; every $\tau$ with $n(\tau)\neq 0$ lies in the $\Gamma_0(N)$-orbit of some $s\in S$; any two points of $S$ in the same $\Gamma_0(N)$-orbit are equal; for each $s\in S$ the cardinality of the stabiliser of $s$ in $\Gamma_0(N)$ divides $2n(s)$; and $\sum_{s\in S} n(s)/\#\mathrm{Stab}_{\Gamma_0(N)}(s)=0$ in $\mathbb C$. Then there exist $V:\mathbb C\to\mathbb C$, a point $b\in\mathfrak H$, a function $m:\mathfrak H\to\mathbb Z$ and functions $F_s:\mathbb C\to\mathbb C$ indexed by $s\in\mathfrak H$ such that: (i) $V(\gamma\tau)=V(\tau)$ for $\gamma\in\Gamma_0(N)$, $\tau\in\mathfrak H$; (ii) for each $\tau\in\mathfrak H$ there is $\Psi$, real-$C^1$ at $\tau$ with $\Psi(\tau)\neq 0$, with $V(z)=(z-\tau)^{n(\tau)}\Psi(z)$ for $z$ near $\tau$; (iii) for each $\sigma\in SL_2(\mathbb Z)$ there is $Y\in\mathbb R$ with $V(\sigma z)=1$ whenever $\operatorname{Im} z>Y$ (points of $\mathbb C$ being viewed in $\mathfrak H$ via `ofComplex`); (iv) for $s\in S$, $F_s$ is continuous with compact support whose topological support lies in $\{\operatorname{Im}>0\}$, and for every pair $E,E'$ with $E'(z)$ a derivative of $E$ at each $z$ of positive imaginary part, $z\mapsto E'(z)F_s(z)$ is integrable with $\int_{\mathbb C}E'F_s=\pi\,(E(s)-E(b))$; (v) $\#\mathrm{Stab}_{\Gamma_0(N)}(s)\cdot m(s)=2n(s)$ for $s\in S$; and (vi) for almost every $z$ with $\operatorname{Im} z>0$, $$\tfrac12\bigl(\partial_1 V(z)+i\,\partial_i V(z)\bigr)/V(z)=\sum_{s\in S}\frac{m(s)}2\;{\textstyle\sum^{\mathrm f}_{\gamma\in\Gamma_0(N)}}F_s(\gamma z)\,\overline{\mathrm{denom}(\gamma,z)^{-2}},$$ the inner sum being a `finsum` over $\Gamma_0(N)$ and the left-hand side the $\bar\partial$-logarithmic derivative expressed through real Fréchet derivatives in the directions $1$ and $i$.
--
--   This is the structural half of the divisor contribution to the reciprocity law for the winding pairing on $X_0(N)$: it produces a $\Gamma_0(N)$-invariant function on $\mathfrak H$, trivial near every cusp, whose divisor is the prescribed degree-zero invariant divisor $n$, together with an explicit expression of its $\bar\partial$-logarithmic derivative as a $\Gamma_0(N)$-periodisation of compactly supported dipole kernels. It is obtained by assembling the local dipole models of [`UpperHalfPlane.exists_localModel_pair_integral_mul_dbarLogDeriv_eq`](thm.html#UpperHalfPlane.exists_localModel_pair_integral_mul_dbarLogDeriv_eq) over coset representatives, and it feeds the limit computation [`ModularCurve.exists_invariant_localModel_tendsto_integral_dbarLogDeriv_smoothedFundamental`](thm.html#ModularCurve.exists_invariant_localModel_tendsto_integral_dbarLogDeriv_smoothedFundamental), where the periodised kernels are unfolded against the smoothed fundamental function.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate.lean

import Mathlib
import Definitions.Def_ModularCurve_SmoothedFundamental

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane MeasureTheory Filter
open scoped MatrixGroups Topology ComplexConjugate

theorem ModularCurve.exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate
    {N : ℕ} [NeZero N] (S : Finset ℍ) (n : ℍ → ℤ)
    (hn : ∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ), n ((γ : SL(2, ℤ)) • τ) = n τ)
    (hcov : ∀ τ : ℍ, n τ ≠ 0 → ∃ s ∈ S, ∃ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • s = τ)
    (hinj : ∀ s ∈ S, ∀ t ∈ S,
      (∃ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • s = t) → s = t)
    (hdvd : ∀ s ∈ S, (Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) s) : ℤ) ∣ 2 * n s)
    (hdeg : ∑ s ∈ S, (n s : ℂ) /
      (Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) s) : ℂ) = 0) :
    ∃ (V : ℂ → ℂ) (b : ℍ) (m : ℍ → ℤ) (F : ℍ → ℂ → ℂ),
      (∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ), V (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) = V τ) ∧
      (∀ τ : ℍ, ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ (τ : ℂ) ∧ Ψ τ ≠ 0 ∧
        V =ᶠ[𝓝 (τ : ℂ)] fun z => (z - τ) ^ (n τ) * Ψ z) ∧
      (∀ σ : SL(2, ℤ), ∃ Y : ℝ, ∀ z : ℂ, Y < z.im → V ((σ • ofComplex z : ℍ) : ℂ) = 1) ∧
      (∀ s ∈ S, Continuous (F s) ∧ HasCompactSupport (F s) ∧ tsupport (F s) ⊆ {z : ℂ | 0 < z.im} ∧
        ∀ E E' : ℂ → ℂ, (∀ z : ℂ, 0 < z.im → HasDerivAt E (E' z) z) →
          Integrable (fun z : ℂ => E' z * F s z) ∧
            ∫ z : ℂ, E' z * F s z = Real.pi * (E s - E b)) ∧
      (∀ s ∈ S, (Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) s) : ℤ) * m s =
        2 * n s) ∧
      ∀ᵐ z : ℂ, 0 < z.im →
        (fderiv ℝ V z 1 + Complex.I * fderiv ℝ V z Complex.I) / 2 / V z =
          ∑ s ∈ S, (m s : ℂ) / 2 * ∑ᶠ γ : CongruenceSubgroup.Gamma0 N,
            F s (((γ : SL(2, ℤ)) • ofComplex z : ℍ) : ℂ) *
              conj (1 / denom ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) (ofComplex z) ^ 2) := by sorry
