-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_exists_ringHom_chartAlgInf_comap_minimalPrimes_ne_of_not_dvd
-- name    : ModularCurve.IgusaScheme.exists_ringHom_chartAlgInf_comap_minimalPrimes_ne_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/8d0e8a7f-b66a-5a33-80a9-624f35bfa8c5
-- title:
--   Pole-chart inclusion X₀(Nq)→ X₀(q) separates components mod q
-- statement:
--   Let $N\ge 1$ and let $q$ be a prime with $q\nmid N$. Write $F_q=$ `modularFunctionFieldFull q` for the subfield of $\mathbb{Q}((t))$ generated over $\mathbb{Q}$ by the $q$-expansions $\mathrm{qExpand}\,\mathbb{Q}\,d\,j$ for the nonzero divisors $d$ of $q$, and $F_{Nq}$ likewise for $Nq$; let $j$ denote the element of each given by the expansion of the modular invariant. Let $A_q$ be the subalgebra of $F_q$ of elements integral over $\mathbb{Z}[j^{-1}]=$ `Algebra.adjoin ℤ {j⁻¹}`, and let $A_{Nq}$ be the subalgebra of $F_{Nq}$ of elements integral over $B[j^{-1}]$, where $B$ is the coefficient ring [`GaloisRep.ratLocalizedAt q`](def/GaloisRep_Flat.html#L8). The assertion is that there is a ring homomorphism $\iota\colon A_q\to A_{Nq}$ such that: (i) for every $b\in A_q$ the Laurent series underlying $\iota(b)$ equals the Laurent series underlying $b$; (ii) $\iota$ sends the distinguished element $j^{-1}$ of $A_q$ to the distinguished element $j^{-1}$ of $A_{Nq}$; and (iii) whenever $P\ne P'$ are two minimal primes over the ideal $qA_{Nq}$, their contractions $\iota^{-1}P$ and $\iota^{-1}P'$ are minimal primes over $qA_q$ and are distinct.
--
--   This is the compatibility, in the charts at infinity, between the integral models of $X_0(q)$ over $\mathbb{Z}$ and of $X_0(Nq)$ over $\mathbb{Z}$ localised at $q$: the inclusion of $q$-expansion fields carries the pole chart of level $q$ into that of level $Nq$, and distinct irreducible components of the fibre at $q$ upstairs lie over distinct components downstairs. It is used in establishing that the two minimal primes over $q$ together with $j^{-1}$ generate the unit ideal in the pole chart of the Igusa scheme at level $Nq$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_exists_ringHom_chartAlgInf_comap_minimalPrimes_ne_of_not_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_ModularCurve_DRModelPackage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve ModularCurve ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.exists_ringHom_chartAlgInf_comap_minimalPrimes_ne_of_not_dvd
    (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) :
    ∃ incl : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull q) (IgusaScheme.jFull q)) →+* ↥(IgusaScheme.chartAlgInf (N * q) q),
      (∀ b, (((incl b : ↥(IgusaScheme.chartAlgInf (N * q) q)) : ↥(modularFunctionFieldFull (N * q))) : LaurentSeries ℚ) =
        ((b : ↥(modularFunctionFieldFull q)) : LaurentSeries ℚ)) ∧
      incl (TwoChartIntegralModel.jInvChartInf ℤ ↥(modularFunctionFieldFull q) (IgusaScheme.jFull q)) =
        IgusaScheme.jInvChartInf (N * q) q ∧
      ∀ P P' : Ideal ↥(IgusaScheme.chartAlgInf (N * q) q),
        P ∈ (Ideal.span {((q : ℕ) : ↥(IgusaScheme.chartAlgInf (N * q) q))}).minimalPrimes →
        P' ∈ (Ideal.span {((q : ℕ) : ↥(IgusaScheme.chartAlgInf (N * q) q))}).minimalPrimes → P ≠ P' →
          Ideal.comap incl P ∈ (Ideal.span {((q : ℕ) : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull q) (IgusaScheme.jFull q)))}).minimalPrimes ∧
          Ideal.comap incl P' ∈ (Ideal.span {((q : ℕ) : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull q) (IgusaScheme.jFull q)))}).minimalPrimes ∧
          Ideal.comap incl P ≠ Ideal.comap incl P' := by sorry
