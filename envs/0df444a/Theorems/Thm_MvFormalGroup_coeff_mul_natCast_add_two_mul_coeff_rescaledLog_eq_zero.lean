-- Prove2me | Theorems.Thm_MvFormalGroup_coeff_mul_natCast_add_two_mul_coeff_rescaledLog_eq_zero
-- name    : MvFormalGroup.coeff_mul_natCast_add_two_mul_coeff_rescaledLog_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/19f8e1b2-1d55-5690-b978-1239b247f64f
-- title:
--   Mixed quadratic coefficients of F and its rescaled logarithm
-- statement:
--   Let $\mathcal O$ be a commutative ring and $p$ a prime whose image in $\mathcal O$ is a non-zero-divisor. Let $F$ be a $d$-dimensional formal group law over $\mathcal O$ in the sense of [`MvFormalGroup`](def/MvFormalGroup_BasicV2.html#L15): a family $F_i$, $i \in \mathrm{Fin}\,d$, of power series in the variables indexed by $\mathrm{Fin}\,d \sqcup \mathrm{Fin}\,d$ with vanishing constant coefficients, with the coefficient of each single left variable $X_{\mathrm{inl}\,j}$ and of each single right variable $X_{\mathrm{inr}\,j}$ in $F_i$ equal to $1$ if $i=j$ and $0$ otherwise, and satisfying the associativity identity between the two threefold substitutions of $F$ into itself. Let $F_p = (F_{p,i})_i$ be a family of power series in the same $2d$ variables with vanishing constant coefficients such that for every $i$ and every non-zero multi-index $m$ one has $\mathrm{coeff}_m(F_{p,i})\cdot p = p^{\deg m}\,\mathrm{coeff}_m(F_i)$ (so $F_p$ plays the role of $F(pA,pB)/p$). Let $\varphi = (\varphi_i)_i$ be power series in $d$ variables with vanishing constant coefficients whose linear part is the identity matrix, i.e. $\mathrm{coeff}_{e_j}(\varphi_i) = \delta_{ij}$, and assume that for each $i$ the substitution of $F_p$ into $\varphi_i$ equals $\varphi_i(X_{\mathrm{inl}\,\bullet}) + \varphi_i(X_{\mathrm{inr}\,\bullet})$. Then for all $i, j \in \mathrm{Fin}\,d$, the coefficient of the mixed monomial $X_{\mathrm{inl}\,j}X_{\mathrm{inr}\,j}$ in $F_i$, multiplied by $p$, plus $2\,\mathrm{coeff}_{2e_j}(\varphi_i)$, vanishes in $\mathcal O$.
--
--   This is the degree-two comparison between a formal group law and the logarithm of its $p$-rescaling: reading off the $X_jY_j$-coefficient of the additivity identity $\varphi\circ F_p = \varphi(A)+\varphi(B)$ relates the mixed quadratic coefficients of $F$ to the pure quadratic coefficients of $\varphi$, an exact identity valid for every $p$. It is used in the construction of the rescaled exponential at $p=2$, where it identifies $\mathrm{coeff}_{2e_j}(\varphi_i)$ with minus the mixed coefficient of $F_i$, via [`MvFormalGroup.exists_rescaledExp_tendsto_zero_of_isLocalRing_cartierDual_of_eq_two`](thm.html#MvFormalGroup.exists_rescaledExp_tendsto_zero_of_isLocalRing_cartierDual_of_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_coeff_mul_natCast_add_two_mul_coeff_rescaledLog_eq_zero.lean

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open MvPowerSeries

universe u

theorem MvFormalGroup.coeff_mul_natCast_add_two_mul_coeff_rescaledLog_eq_zero
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    {d : ℕ} (F : MvFormalGroup d 𝓞)
    (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞)
    (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
      (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m)
    (hFp0 : ∀ i, (Fp i).constantCoeff = 0)
    (φ : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hφ0 : ∀ i, (φ i).constantCoeff = 0)
    (hφ1 : MvFormalGroup.linearPart φ = 1)
    (hφF : ∀ i, subst Fp (φ i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
        subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i))
    (i j : Fin d) :
    (F.toPowerSeries i).coeff (Finsupp.single (Sum.inl j) 1 + Finsupp.single (Sum.inr j) 1) * (p : 𝓞) +
      2 * (φ i).coeff (Finsupp.single j 2) = 0 := by sorry
