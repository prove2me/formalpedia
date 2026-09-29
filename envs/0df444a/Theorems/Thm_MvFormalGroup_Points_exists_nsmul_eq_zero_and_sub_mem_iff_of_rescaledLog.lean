-- Prove2me | Theorems.Thm_MvFormalGroup_Points_exists_nsmul_eq_zero_and_sub_mem_iff_of_rescaledLog
-- name    : MvFormalGroup.Points.exists_nsmul_eq_zero_and_sub_mem_iff_of_rescaledLog
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/8f0113a7-5ad9-5908-b065-0bb1a63b6ab5
-- title:
--   Integral logarithm criterion for p^v-torsion congruence
-- statement:
--   Let $\mathcal O$ be a commutative ring, $p$ a prime whose image in $\mathcal O$ is a non-zero-divisor, and let $F$ be a $d$-dimensional formal group law over $\mathcal O$: a $d$-tuple `F.toPowerSeries` of power series in the variables indexed by $\mathrm{Fin}\,d\oplus\mathrm{Fin}\,d$ with vanishing constant terms, linear coefficients $\delta_{ij}$ in each of the two blocks of variables, and the associativity identity; $F$ is assumed commutative, i.e. invariant under exchanging the two blocks. Let $F_p$ be a $d$-tuple of power series in the same variables with vanishing constant terms such that for every $i$ and every non-zero multidegree $m$ one has $\mathrm{coeff}_m(F_{p,i})\cdot p = p^{\deg m}\,\mathrm{coeff}_m(F_i)$ (so $F_p$ is the rescaled law $F(pA,pB)/p$). Let $\varphi,\psi$ be $d$-tuples of power series in $d$ variables over $\mathcal O$ with vanishing constant terms, such that the matrix of linear coefficients of $\varphi$ is the identity, the coefficients of $\varphi$ and of $\psi$ tend $p$-adically to $0$ (for each $N$ and $i$, all but finitely many coefficients lie in $(p^N)$), $\varphi$ is additive for $F_p$, i.e. $\varphi_i\circ F_p=\varphi_i(A)+\varphi_i(B)$, and $\varphi,\psi$ are mutually inverse under substitution. Let $Y$ be a commutative $\mathcal O$-algebra, finite and free as an $\mathcal O$-module and $(p)$-adically complete, and let $y$ be a point of $F$ over $Y$ with values in the radical of $(p)$, i.e. a $d$-tuple $y_i\in\sqrt{(p)}$, the set of such tuples being a group under $F$. Let $v\in\mathbb N$ and $w'\colon \mathrm{Fin}\,d\to Y$ with $(p^v\cdot y)_i = p\,w'_i$ for all $i$. Then there exists a point $y'$ of $F$ over $Y$ with values in $\sqrt{(p)}$ satisfying $p^v\cdot y'=0$ and $y'_i-y_i\in(p)$ for all $i$, if and only if there is an $n_0$ such that for all $n\ge n_0$, all $i$, and every polynomial $P\in\mathcal O[X_1,\dots,X_d]$ whose coefficient at $m$ is $\mathrm{coeff}_m(\varphi_i)$ when $m_j<n$ for all $j$ and $0$ otherwise, the value $P(w')\in Y$ lies in $(p^v)$.
--
--   This is the integral form of the logarithm criterion: a point $y$ with $p^v\cdot y$ divisible by $p$ is congruent modulo $pY$ to a $p^v$-torsion point exactly when the rescaled logarithm $\varphi$, evaluated at $(p^v\cdot y)/p$ through its box truncations, takes values in $p^vY$. It is used in the construction of algebra homomorphisms prescribed modulo the Fontaine kernel attached to a formal group, in [`Deformation.exists_algHom_baseChange_eq_of_forall_map_mem_fontaineKer_of_mvFormalGroup`](thm.html#Deformation.exists_algHom_baseChange_eq_of_forall_map_mem_fontaineKer_of_mvFormalGroup).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_Points_exists_nsmul_eq_zero_and_sub_mem_iff_of_rescaledLog.lean

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MvPowerSeries

universe u w

theorem MvFormalGroup.Points.exists_nsmul_eq_zero_and_sub_mem_iff_of_rescaledLog
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm]
    (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞)
    (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
      (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m)
    (hFp0 : ∀ i, (Fp i).constantCoeff = 0)
    (φ ψ : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hφ0 : ∀ i, (φ i).constantCoeff = 0) (hψ0 : ∀ i, (ψ i).constantCoeff = 0)
    (hφ1 : MvFormalGroup.linearPart φ = 1)
    (hφT : ∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite, (φ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N})
    (hψT : ∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite, (ψ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N})
    (hφF : ∀ i, subst Fp (φ i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
        subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i))
    (hψφ : ∀ i, subst φ (ψ i) = X i) (hφψ : ∀ i, subst ψ (φ i) = X i)
    (Y : Type w) [CommRing Y] [Algebra 𝓞 Y] [Module.Finite 𝓞 Y] [Module.Free 𝓞 Y]
    [IsAdicComplete (Ideal.span {(p : Y)}) Y]
    (y : MvFormalGroup.Points F Y (Ideal.span {(p : Y)})) (v : ℕ)
    (w' : Fin d → Y) (hw' : ∀ i, (p ^ v • y).val i = (p : Y) * w' i) :
    (∃ y' : MvFormalGroup.Points F Y (Ideal.span {(p : Y)}),
        p ^ v • y' = 0 ∧ ∀ i, y'.val i - y.val i ∈ Ideal.span {(p : Y)}) ↔
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ (i : Fin d) (P : MvPolynomial (Fin d) 𝓞),
        (∀ m : Fin d →₀ ℕ, P.coeff m = if ∀ j, m j < n then (φ i).coeff m else 0) →
          MvPolynomial.aeval w' P ∈ Ideal.span {(p : Y) ^ v} := by sorry
