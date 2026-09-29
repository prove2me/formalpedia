-- Prove2me | Theorems.Thm_ModularCurve_exists_continuous_pow_eq_of_isPrincipal_smul_cuspidalDivisor
-- name    : ModularCurve.exists_continuous_pow_eq_of_isPrincipal_smul_cuspidalDivisor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/ba546285-c9d7-52c5-9737-8893c6c4c7cd
-- title:
--   Principal multiple of the cuspidal divisor gives an invariant (Δ/Δ(ℓ ·))^m branch
-- statement:
--   Let $\ell$ be a prime and $m$ a positive natural number. Work in the field $F =$ `modularFunctionFieldBar ℓ`, the base change to $\overline{\mathbb Q}$ of the full modular function field of level $\ell$ inside Laurent series, viewed as an extension of $K = \overline{\mathbb Q}$; its divisors are finitely supported $\mathbb Z$-valued functions on the set of places of $F/K$ (valuation subrings of $F$ containing $K$, proper, and principal ideal rings), and a divisor $D$ is principal when there is $f \in F$, $f \neq 0$, with $D(v) = v.\mathrm{ord}(f)$ for every place $v$. The hypothesis is that $m \cdot \big((\bar 0) - (\bar\infty)\big)$ is principal, where $(\bar\infty)$ is the place `cuspInftyBar ℓ` attached to the order of vanishing in the Laurent parameter and $(\bar 0)$ is its image under the Fricke involution. The conclusion asserts the existence of a function $H \colon \mathfrak H \to \mathbb C$ that is continuous (no holomorphy is claimed), satisfies $H(\tau)^{\ell-1} = \big(\Delta(\tau)/\Delta(\gamma_\ell \cdot \tau)\big)^m$ for all $\tau$ in the upper half-plane, where $\gamma_\ell \in \mathrm{GL}_2(\mathbb R)$ is the matrix $\begin{pmatrix}\ell & 0\\ 0 & 1\end{pmatrix}$ (so $\gamma_\ell \cdot \tau = \ell\tau$), and is invariant under $\Gamma_0(\ell)$: $H(\gamma \cdot \tau) = H(\tau)$ for all $\gamma \in \Gamma_0(\ell)$ and all $\tau$.
--
--   This is the passage from the algebraic side (the cuspidal class of $X_0(\ell)$ is killed by $m$) to the analytic side, producing a $\Gamma_0(\ell)$-invariant branch of $(\Delta(\tau)/\Delta(\ell\tau))^{m/(\ell-1)}$ built from the logarithmic transformation law of the Dedekind $\eta$-function and Dedekind sums. It feeds the computation of the exact order of the cuspidal class, [`ModularCurve.addOrderOf_cuspidalClass_eq_eisensteinNumerator`](thm.html#ModularCurve.addOrderOf_cuspidalClass_eq_eisensteinNumerator).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_continuous_pow_eq_of_isPrincipal_smul_cuspidalDivisor.lean

import Definitions.Def_ModularCurve_EtaQuotient
import Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.exists_continuous_pow_eq_of_isPrincipal_smul_cuspidalDivisor (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (m : ℕ) (hm : 0 < m) (hP : AlgebraicCurve.Divisor.IsPrincipal ((m : ℤ) • ModularCurve.cuspidalDivisor ℓ)) : ∃ H : UpperHalfPlane → ℂ, Continuous H ∧ (∀ τ : UpperHalfPlane, H τ ^ (ℓ - 1) = (ModularForm.discriminant τ / ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • τ)) ^ m) ∧ ∀ γ ∈ CongruenceSubgroup.Gamma0 ℓ, ∀ τ : UpperHalfPlane, H (γ • τ) = H τ := by sorry
