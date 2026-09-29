-- Prove2me | Theorems.Thm_MvFormalGroup_exists_rescaledExp_tendsto_zero_of_ne_two
-- name    : MvFormalGroup.exists_rescaledExp_tendsto_zero_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/3be08db2-251a-5321-b361-dca68c9f8eb1
-- title:
--   Rescaled exponential with p-adically vanishing coefficients, p odd
-- statement:
--   Let $\mathcal O$ be a commutative ring, $p$ a prime with $p \ne 2$ whose image in $\mathcal O$ is a non-zero-divisor, and assume $\mathcal O$ is adically complete for the ideal $(p)$. Let $d \in \mathbb N$ and let $F$ be a $d$-dimensional formal group law over $\mathcal O$, i.e. a $d$-tuple $F_i \in \mathcal O[[A_1,\dots,A_d,B_1,\dots,B_d]]$ (variables indexed by $\mathrm{Fin}\,d \oplus \mathrm{Fin}\,d$) with zero constant terms, with the linear coefficient of $A_j$ and of $B_j$ in $F_i$ equal to $\delta_{ij}$, and satisfying the associativity identity $F(F(A,B),C) = F(A,F(B,C))$ as a substitution identity; $F$ is assumed commutative, in the sense that interchanging the two blocks of variables fixes each $F_i$. Let $F_p$ be a $d$-tuple of power series in the same $2d$ variables with zero constant terms whose coefficients satisfy $\mathrm{coeff}_m(F_{p,i})\cdot p = p^{\deg m}\,\mathrm{coeff}_m(F_i)$ for every $m \ne 0$, and let $\varphi$ be a $d$-tuple of power series in $X_1,\dots,X_d$ with zero constant terms whose matrix of linear coefficients is the identity and which satisfies $\varphi \circ F_p = \varphi(A) + \varphi(B)$, i.e. $\mathrm{subst}\,F_p\,(\varphi_i)$ equals the sum of the two substitutions of $\varphi_i$ into the first and into the second block of variables. Then there exists a $d$-tuple $\psi$ of power series in $X_1,\dots,X_d$ over $\mathcal O$ such that each $\psi_i$ has zero constant term; for every $N$ and every $i$, all but finitely many coefficients of $\psi_i$ lie in the ideal $(p^N)$; and $\psi$ and $\varphi$ are two-sided substitutional inverses, $\mathrm{subst}\,\varphi\,(\psi_i) = X_i$ and $\mathrm{subst}\,\psi\,(\varphi_i) = X_i$.
--
--   The tuple $\varphi$ is the rescaled logarithm of $F$ and $\psi$ its rescaled exponential; the assertion is that for odd $p$ the exponential exists integrally over any $p$-adically complete $\mathcal O$ and has $p$-adically vanishing coefficients, the denominators of the inverse of the logarithm being divisors of the multinomial factorials. The four conjuncts are exactly the hypotheses on $\psi$ required by the lifting and integral-logarithm criteria used later; the statement is cited by [`MvFormalGroup.exists_rescaledExp_tendsto_zero_of_isLocalRing_cartierDual`](thm.html#MvFormalGroup.exists_rescaledExp_tendsto_zero_of_isLocalRing_cartierDual).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_exists_rescaledExp_tendsto_zero_of_ne_two.lean

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MvPowerSeries

universe u

theorem MvFormalGroup.exists_rescaledExp_tendsto_zero_of_ne_two
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    (hp2 : p ≠ 2)
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm]
    (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞)
    (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
      (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m)
    (hFp0 : ∀ i, (Fp i).constantCoeff = 0)
    (φ : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hφ0 : ∀ i, (φ i).constantCoeff = 0)
    (hφ1 : MvFormalGroup.linearPart φ = 1)
    (hφF : ∀ i, subst Fp (φ i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
        subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i)) :
    ∃ ψ : Fin d → MvPowerSeries (Fin d) 𝓞,

      (∀ i, (ψ i).constantCoeff = 0) ∧

      (∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite, (ψ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N}) ∧

      (∀ i, subst φ (ψ i) = X i) ∧

      (∀ i, subst ψ (φ i) = X i) := by sorry
