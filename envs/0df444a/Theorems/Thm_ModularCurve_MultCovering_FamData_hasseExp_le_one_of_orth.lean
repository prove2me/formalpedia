-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_FamData_hasseExp_le_one_of_orth
-- name    : ModularCurve.MultCovering.FamData.hasseExp_le_one_of_orth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/baa786e5-3f68-51be-8eb5-67c109715123
-- title:
--   Hasse exponent at most one for doubly orthogonal bases
-- statement:
--   Fix a prime $p$ with $5 \le p$, a natural number $r$, and $D : \mathrm{FamData}\ p\ r$, i.e. a family $D.\mathrm{tRat}$ of $r$ elements of the rational modular function field $\mathrm{modularFunctionFieldFull}\,(1\cdot p)$ together with the corresponding family $D.t$ obtained from it by the coefficient embedding into $\mathrm{modularFunctionFieldBar}\,(1\cdot p)$. Assume: (i) $D.t\,l = 1$ for the index $l$ with $l = 0$; (ii) `IsEmbBasis`, i.e. the $D.t\,l$ are linearly independent over $\overline{\mathbb{Q}}$ and span the Riemann–Roch space $\{f : v(f) \le \exp(\mathrm{embDivisor}\,(1\cdot p)\,v)\ \text{for all places } v\}$; (iii) orthogonality at $\infty$: for each $c : \mathrm{Fin}\,r \to \mathbb{Q}$, all Laurent coefficients of $\sum_i c_i\, D.\mathrm{tRat}\,i$ have non-negative $p$-adic valuation if and only if $v_p(c_i) \ge 0$ for all $i$; (iv) orthogonality at $0$: the same for $\sum_i c_i\,\mathrm{frickeInvolutionFull}\,(1\cdot p)\,(D.\mathrm{tRat}\,i)$, but with the condition $v_p(c_i) \ge -\mathrm{hasseExp}\,D\,i$, where $\mathrm{hasseExp}\,D\,i$ is the truncation to $\mathbb{N}$ of $\mathrm{hasseContent}\,D\,i$. Let further $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, its residue field of characteristic $p$ and with decidable equality, $\Gamma$ a chart context for $p$ and $A$, and $\Delta$ an annulus context over $\Gamma$ (pairs of annuli with common domain and modulus $p^{\mathrm{jWidth}}$, product of parameters the modulus, domains the supersingular-centred places at the values $\mathrm{ssValue}\,\Gamma\,e$, each attached to the source and target charts at the corresponding nodes). Assume finally $\mathrm{ssValue}\,\Gamma\,e \ne 0$ and $\ne 1728$ for every $e$. Then $\mathrm{hasseExp}\,D\,l \le 1$ for every $l$.
--
--   This is the width-one bound $n_l \le 1$ on the $p$-adic content of the $q$-expansions at the cusp $0$ of a rational basis of the relevant Riemann–Roch space on $X_0(p)$, obtained by comparing the two Deligne–Rapoport components across the supersingular annuli. It supplies the integrality input used by [`ModularCurve.MultCovering.FamData.t_zeroChart_of_orth`](thm.html#ModularCurve.MultCovering.FamData.t_zeroChart_of_orth) in the identification of the family on the chart at the cusp $0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_FamData_hasseExp_le_one_of_orth.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringAnnuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve IsLocalRing ModularCurve.MultCovering

theorem ModularCurve.MultCovering.FamData.hasseExp_le_one_of_orth (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {r : ℕ} (D : FamData p r)
    (hzero : ∀ l : Fin r, (l : ℕ) = 0 → D.t l = 1)
    (hbasis : IsEmbBasis (1 * p) D.t)
    (horthInf : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • D.tRat i : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, 0 ≤ padicValRat p (c i))
    (horthZero : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • frickeInvolutionFull (1 * p) (D.tRat i) :
        ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, -((hasseExp D i : ℕ) : ℤ) ≤ padicValRat p (c i))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    (hw1 : ∀ e, ssValue Γ e ≠ 0 ∧ ssValue Γ e ≠ 1728) :
    ∀ l : Fin r, hasseExp D l ≤ 1 := by sorry
