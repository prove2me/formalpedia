-- Prove2me | Theorems.Thm_MvPowerSeries_exists_forall_coeff_mul_eq_pow_mul_and_residue_eq_coeff_mul_of_weightedInitialForm_ne_zero
-- name    : MvPowerSeries.exists_forall_coeff_mul_eq_pow_mul_and_residue_eq_coeff_mul_of_weightedInitialForm_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/fbedcdcc-349a-55d2-9bdf-e07c2faf6e1c
-- title:
--   Weighted initial form of a multiple is a multiple of the initial form
-- statement:
--   Let $\sigma$ be a finite type of variables and let $O$ be a discrete valuation ring (a commutative domain, local and principal in Mathlib's sense) with residue field $\kappa$, let $\pi \in O$ be irreducible, let $m \ge 1$, and let $r, c$ be natural numbers. Let $\rho, H \in O[[X_\sigma]]$ and let $\bar\rho \in \kappa[X_\sigma]$ be a non-zero polynomial. Assume: (i) for every exponent $e : \sigma \to_0 \mathbb{N}$ with $m\,|e| \le r$, where $|e|$ is the total degree of $e$, the coefficient of $X^e$ in $\rho$ can be written $\pi^{r - m|e|} a$ with $a \in O$ reducing to the coefficient of $X^e$ in $\bar\rho$; (ii) the coefficient of $X^e$ in $\bar\rho$ vanishes whenever $r < m|e|$; (iii) for every $e$, the coefficient of $X^e$ in $H\rho$ lies in $\mathfrak{m}_O^{\,c - m|e|}$, the exponent being truncated subtraction in $\mathbb{N}$. The conclusion asserts the existence of $Q \in \kappa[X_\sigma]$ such that, for every $e$ with $m|e| \le c$, the coefficient of $X^e$ in $H\rho$ equals $\pi^{c - m|e|} a$ for some $a \in O$ whose residue is the coefficient of $X^e$ in $Q\bar\rho$, and such that the coefficient of $X^e$ in $Q\bar\rho$ vanishes whenever $c < m|e|$.
--
--   This is the multiplicativity statement for initial forms with respect to the weighted order on $O[[X_\sigma]]$ in which $\pi$ has weight $1$ and each variable has weight $m$: if $\rho$ has order at least $r$ with initial form $\bar\rho$ and $H\rho$ has order at least $c$, then the degree-$c$ initial form of $H\rho$ is divisible by $\bar\rho$ in $\kappa[X_\sigma]$. It is used in the identification of the special fibre of a weighted blow-up chart of a hypersurface $O[[X_\sigma]]/(\rho)$, via [`DrinfeldCurve.LocalChart.exists_isPrime_algEquiv_coordRing_blowupChart_quotient_of_mem_maximalIdeal`](thm.html#DrinfeldCurve.LocalChart.exists_isPrime_algEquiv_coordRing_blowupChart_quotient_of_mem_maximalIdeal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPowerSeries_exists_forall_coeff_mul_eq_pow_mul_and_residue_eq_coeff_mul_of_weightedInitialForm_ne_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem MvPowerSeries.exists_forall_coeff_mul_eq_pow_mul_and_residue_eq_coeff_mul_of_weightedInitialForm_ne_zero
    (σ : Type u) [Finite σ] (O : Type v) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) (hπ : Irreducible π) (m : ℕ) (hm : 1 ≤ m) (r c : ℕ)
    (ρ H : MvPowerSeries σ O) (ρbar : MvPolynomial σ (IsLocalRing.ResidueField O)) (hρbar : ρbar ≠ 0)
    (hρ : ∀ e : σ →₀ ℕ, m * e.degree ≤ r →
      ∃ a : O, MvPowerSeries.coeff e ρ = π ^ (r - m * e.degree) * a ∧
        IsLocalRing.residue O a = MvPolynomial.coeff e ρbar)
    (hρ' : ∀ e : σ →₀ ℕ, r < m * e.degree → MvPolynomial.coeff e ρbar = 0)
    (hHρ : ∀ e : σ →₀ ℕ, MvPowerSeries.coeff e (H * ρ) ∈ IsLocalRing.maximalIdeal O ^ (c - m * e.degree)) :
    ∃ Q : MvPolynomial σ (IsLocalRing.ResidueField O),
      (∀ e : σ →₀ ℕ, m * e.degree ≤ c →
        ∃ a : O, MvPowerSeries.coeff e (H * ρ) = π ^ (c - m * e.degree) * a ∧
          IsLocalRing.residue O a = MvPolynomial.coeff e (Q * ρbar)) ∧
      (∀ e : σ →₀ ℕ, c < m * e.degree → MvPolynomial.coeff e (Q * ρbar) = 0) := by sorry
