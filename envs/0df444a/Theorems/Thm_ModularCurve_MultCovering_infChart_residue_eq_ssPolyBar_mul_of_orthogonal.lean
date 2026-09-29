-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_infChart_residue_eq_ssPolyBar_mul_of_orthogonal
-- name    : ModularCurve.MultCovering.infChart_residue_eq_ssPolyBar_mul_of_orthogonal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/5992f0b5-7f9e-528f-9e7c-15993083bcb9
-- title:
--   Cusp-chart residues of a p-adically orthogonal family on X₀(p)
-- statement:
--   Let $p\ge 5$ be a prime, put $m=\mathrm{mAnnuli}(p)=\lfloor p/12\rfloor+[p\equiv 2\ (3)]+[p\equiv 3\ (4)]$, let $r=m+1$, and let $g:\mathrm{Fin}\,r\to F$ be a family in the rational modular function field $F=\mathtt{modularFunctionFieldFull}(1\cdot p)\subseteq\mathbb Q((q))$, subject to: $g_l=1$ whenever $l=0$; for every $l$, the coefficientwise base change $\mathtt{coeffEmb}(g_l)$, viewed in $\mathtt{modularFunctionFieldBar}(1\cdot p)$ over $\overline{\mathbb Q}$, lies in the Riemann–Roch space of $\mathtt{embDivisor}(1\cdot p)=\mathtt{embDegree}(1\cdot p)\cdot[\overline\infty]$, i.e. its adic valuation at every place $v$ is at most $\exp$ of that divisor's value at $v$; a $p$-adic orthogonality condition, namely for every $c:\mathrm{Fin}\,r\to\mathbb Q$ all Laurent coefficients of $\sum_i c_i g_i$ have non-negative $p$-adic valuation if and only if every $c_i$ does; and for every $l\ge 1$ all Laurent coefficients of $p^{-1}\,\mathtt{frickeInvolutionFull}(1\cdot p)(g_l)$ have non-negative $p$-adic valuation. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a non-unit of $A$, residue field $k$ of characteristic $p$, and let $\Gamma$ be a chart context $\mathtt{ChartCtx}\,p\,A$. Then every $\mathtt{coeffEmb}(g_l)$ is integral for the chart $\mathtt{infChart}\,\Gamma$, and for these memberships: the residue of $g_l$ is $1$ for $l=0$, and there are polynomials $P_l\in k[X]$ such that for $l\ge 1$ one has $\deg P_l+1\le m$ and $\overline{g_l}=\mathtt{ssPolyBar}\,\Gamma\cdot P_l(\bar\jmath)$, where $\mathtt{ssPolyBar}\,\Gamma=\prod_{e:\mathrm{Fin}\,m}(\bar\jmath-\mathtt{ssValue}\,\Gamma\,e)$ and $\bar\jmath$ is the image of $j$ in $\mathtt{modularFunctionFieldC}\,k\,1$; moreover $(P_l)_{l\ge 1}$ is linearly independent over $k$ and spans $k[X]_{<m}$.
--
--   This is the clause at the cusp $\overline\infty$ of the family data attached to the degeneration of $X_0(p)$ at $p$: a $p$-adically orthogonal rational basis of the Riemann–Roch space of $\mathtt{embDegree}\cdot[\overline\infty]$, with the Fricke-side integrality condition, reduces on the first component to $1$ together with the supersingular polynomial times a basis of polynomials of degree $<m$ in $\bar\jmath$. It is used in the construction of family contexts for the multiplicative covering and in the resulting bound on the Hasse exponent.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_infChart_residue_eq_ssPolyBar_mul_of_orthogonal.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve.MultCovering
open ModularCurve hiding jBar

theorem ModularCurve.MultCovering.infChart_residue_eq_ssPolyBar_mul_of_orthogonal
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    {r : ℕ} (hr : r = mAnnuli p + 1) (g : Fin r → ↥(modularFunctionFieldFull (1 * p)))
    (hg0 : ∀ l : Fin r, (l : ℕ) = 0 → g l = 1)
    (hW : ∀ l : Fin r, (⟨coeffEmb (AlgebraicClosure ℚ) ↑(g l), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (g l).2⟩ : ↥(modularFunctionFieldBar (1 * p))) ∈ riemannRochSpace (embDivisor (1 * p)))
    (horth : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • g i : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, 0 ≤ padicValRat p (c i))
    (h0 : ∀ l : Fin r, 1 ≤ (l : ℕ) → ∀ m : ℤ, 0 ≤ padicValRat p
      ((p : ℚ)⁻¹ * ((frickeInvolutionFull (1 * p) (g l) : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) :
    ∃ hint : ∀ l, (⟨coeffEmb (AlgebraicClosure ℚ) ↑(g l), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (g l).2⟩ : ↥(modularFunctionFieldBar (1 * p))) ∈ (infChart Γ).integers,
      (∀ l : Fin r, (l : ℕ) = 0 → (infChart Γ).residue ⟨(⟨coeffEmb (AlgebraicClosure ℚ) ↑(g l), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (g l).2⟩ : ↥(modularFunctionFieldBar (1 * p))), hint l⟩ = 1) ∧
      ∃ P : Fin r → Polynomial (IsLocalRing.ResidueField ↥A),
        (∀ l : Fin r, 1 ≤ (l : ℕ) →
          (P l).natDegree + 1 ≤ mAnnuli p ∧
          (infChart Γ).residue ⟨(⟨coeffEmb (AlgebraicClosure ℚ) ↑(g l), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (g l).2⟩ : ↥(modularFunctionFieldBar (1 * p))), hint l⟩
            = ssPolyBar Γ * Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P l)) ∧
        LinearIndependent (IsLocalRing.ResidueField ↥A) (fun l : {l : Fin r // 1 ≤ (l : ℕ)} => P l) ∧
        Submodule.span (IsLocalRing.ResidueField ↥A) (Set.range fun l : {l : Fin r // 1 ≤ (l : ℕ)} => P l)
          = Polynomial.degreeLT (IsLocalRing.ResidueField ↥A) (mAnnuli p) := by sorry
