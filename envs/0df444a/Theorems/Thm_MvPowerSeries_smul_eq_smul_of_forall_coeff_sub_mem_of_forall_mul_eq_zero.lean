-- Prove2me | Theorems.Thm_MvPowerSeries_smul_eq_smul_of_forall_coeff_sub_mem_of_forall_mul_eq_zero
-- name    : MvPowerSeries.smul_eq_smul_of_forall_coeff_sub_mem_of_forall_mul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/c3f52cb8-5c96-51ad-ab84-de4926ff791c
-- title:
--   Scalars annihilating an ideal see power series modulo it
-- statement:
--   Let $R$ be a commutative ring and $\tau$ an index type, and let $M$ be an ideal of $R$ and $j \in R$ an element with $m \cdot j = 0$ for every $m \in M$. Let $g, g'$ be multivariate formal power series in $\mathrm{MvPowerSeries}\ \tau\ R$, that is, functions on the monoid of finitely supported maps $\tau \to \mathbb{N}$ with values in $R$, and suppose that for every exponent $n$ the difference of coefficients $\mathrm{coeff}\ n\ g - \mathrm{coeff}\ n\ g'$ lies in $M$. Then the scalar multiples agree: $j \bullet g = j \bullet g'$ in $\mathrm{MvPowerSeries}\ \tau\ R$. In other words, multiplication by an element annihilated by $M$ factors through coefficientwise reduction modulo $M$; the hypothesis on $j$ is stated as annihilation of each element of $M$ on the right, and the congruence hypothesis is required at every multi-index, with no finiteness or Noetherian assumption on $R$, $M$ or $\tau$.
--
--   This is the elementary observation underlying the small-extension calculus: for a surjection of local rings with kernel $J$ satisfying $J\mathfrak{m} = 0$, multiplication by an element of $J$ depends only on residues. It is used in the deformation-theoretic results [`MvFormalGroup.Deformation.existsUnique_isShiftBy`](thm.html#MvFormalGroup.Deformation.existsUnique_isShiftBy), [`MvFormalGroup.Deformation.exists_isComm_isShiftBy`](thm.html#MvFormalGroup.Deformation.exists_isComm_isShiftBy) and [`MvFormalGroup.Deformation.isIso_of_isShiftBy_of_isShiftBy`](thm.html#MvFormalGroup.Deformation.isIso_of_isShiftBy_of_isShiftBy), where it makes first-order data independent of the chosen lifts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPowerSeries_smul_eq_smul_of_forall_coeff_sub_mem_of_forall_mul_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u w

theorem MvPowerSeries.smul_eq_smul_of_forall_coeff_sub_mem_of_forall_mul_eq_zero
    {R : Type u} [CommRing R] {τ : Type w} (M : Ideal R) (j : R) (hj : ∀ m ∈ M, m * j = 0)
    (g g' : MvPowerSeries τ R) (h : ∀ n, MvPowerSeries.coeff n g - MvPowerSeries.coeff n g' ∈ M) :
    j • g = j • g' := by sorry
