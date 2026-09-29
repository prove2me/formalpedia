-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_exists_famCtx_toFamData_eq_of_bifiltered
-- name    : ModularCurve.MultCovering.exists_famCtx_toFamData_eq_of_bifiltered
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/5a910560-c3aa-5dec-b2f3-77b3adae88dd
-- title:
--   Bi-filtered unimodular recombination of a good family
-- statement:
--   Fix a prime $p$ and $r \in \mathbb{N}$, and let $\Phi$ be a family context `FamCtx p r` for level $1 \cdot p$: family data consisting of $t_l \in \overline{\mathcal{F}} =$ `modularFunctionFieldBar (1 * p)` and rational expansions $\tau_l \in$ `modularFunctionFieldFull (1 * p)` with $t_l$ the coefficientwise base change of $\tau_l$, such that $(t_l)$ is an embedding basis (linearly independent over $\overline{\mathbb{Q}}$ and spanning the Riemann–Roch space of the embedding divisor), $t_l = 1$ whenever $l = 0$, together with the two chart conditions at the $\bar\infty$- and $\bar 0$-charts of `FamCtx`. Write $n_l =$ `hasseExp Φ.toFamData l`. Two orthogonality hypotheses are assumed: for every $c : \mathrm{Fin}\,r \to \mathbb{Q}$, all Laurent coefficients of $\sum_i c_i \tau_i$ are $p$-integral iff $v_p(c_i) \ge 0$ for all $i$; and all Laurent coefficients of $\sum_i c_i\,\iota(\tau_i)$ are $p$-integral iff $v_p(c_i) \ge -n_i$ for all $i$, where $\iota$ is `frickeInvolutionFull (1 * p)` (the chosen $\mathbb{Q}$-automorphism satisfying `IsFrickeAutFull`, the identity if none exists). Let $U$ be an invertible $r \times r$ rational matrix such that each entry of $U$ and of $U^{-1}$ is zero or has $v_p \ge \max(0, n_i - n_j)$, and with $U_{ij} = \delta_{j0}$ for $i = 0$. Let $D'$ be family data with $D'.\tau_i = \sum_j U_{ij}\tau_j$, $D'.t_i = \sum_j U_{ij} t_j$ (the coefficients mapped into $\overline{\mathcal{F}}$), and `hasseExp D' l` $= n_l$ for all $l$. Then $D'$ underlies some family context $\Phi' :$ `FamCtx p r`, i.e. $\Phi'.\mathrm{toFamData} = D'$.
--
--   This is the stability of the good-family structure on the multiplicative covering of $X_0(p)$ under a rational change of basis respecting the two $p$-adic filtrations attached to the $\bar\infty$- and $\bar 0$-charts: the conditions on $U$ and $U^{-1}$ say that $U$ preserves both lattices $\langle t_l \rangle$ and $\langle p^{-n_l} t_l \rangle$ over $\mathbb{Z}_{(p)}$ while fixing the member $t_0 = 1$. It is the adapter used by the cross-comparison results for the $\bar\infty$- and $\bar 0$-charts, which replace a given family by a recombined one before comparing residues.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_exists_famCtx_toFamData_eq_of_bifiltered.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_ModularCurve_MultCoveringFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.exists_famCtx_toFamData_eq_of_bifiltered (p : ℕ) [Fact p.Prime] {r : ℕ} (Φ : FamCtx p r)
    (horthInf : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • Φ.toFamData.tRat i : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, 0 ≤ padicValRat p (c i))
    (horthZero : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • frickeInvolutionFull (1 * p) (Φ.toFamData.tRat i) :
          ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, -((hasseExp Φ.toFamData i : ℕ) : ℤ) ≤ padicValRat p (c i))
    (U : Matrix (Fin r) (Fin r) ℚ) (hUunit : IsUnit U)
    (hU : ∀ i j, max 0 ((hasseExp Φ.toFamData i : ℤ) - (hasseExp Φ.toFamData j : ℤ)) ≤ padicValRat p (U i j) ∨ U i j = 0)
    (hUinv : ∀ i j, max 0 ((hasseExp Φ.toFamData i : ℤ) - (hasseExp Φ.toFamData j : ℤ)) ≤ padicValRat p (U⁻¹ i j) ∨ U⁻¹ i j = 0)
    (hU0 : ∀ i j : Fin r, (i : ℕ) = 0 → U i j = if (j : ℕ) = 0 then 1 else 0)
    (D' : FamData p r)
    (htRat : ∀ i, D'.tRat i = ∑ j, U i j • Φ.tRat j)
    (ht : ∀ i, D'.t i = ∑ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
        (algebraMap ℚ (AlgebraicClosure ℚ) (U i j)) * Φ.t j)
    (hexp : ∀ l, hasseExp D' l = hasseExp Φ.toFamData l) :
    ∃ Φ' : FamCtx p r, Φ'.toFamData = D' := by sorry
