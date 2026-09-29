-- Prove2me | Theorems.Thm_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC_of_liesOverPrime
-- name    : ModularCurve.exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC_of_liesOverPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/382452ce-adcb-5c09-8171-b7b3a2f5633b
-- title:
--   Gauss valuation ring on ℚ̄· F(Γ) at a place above p
-- statement:
--   Let $\Gamma$ be a finite-index subgroup of $\mathrm{SL}_2(\mathbb Z)$ containing the translation matrix $T$, let $p$ be a prime, and let $A$ be a valuation subring of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` which lies over $p$ in the sense that $p$, viewed in $\overline{\mathbb Q}$, is a non-unit of $A$. Write $F(\Gamma) =$ `qExpFunctionFieldC ℚ Γ` for the subfield of $\mathbb Q((q))$ generated over $\mathbb Q$ by all quotients $\mathrm{intSeriesC}\,p_f / \mathrm{intSeriesC}\,p_g$, where $p_f, p_g$ are integral $q$-expansions of modular forms $f, g$ of some common weight $k$ for $\Gamma$ and the denominator is non-zero, and write $F =$ `laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)` for the subfield of $\overline{\mathbb Q}((q))$ generated over $\overline{\mathbb Q}$ by the coefficientwise image of $F(\Gamma)$. The assertion is that there exists a valuation subring $W_0$ of $F$ with three properties: (i) an element $f$ of $F$ lies in $W_0$ if and only if there are power series $x, y \in A[[q]]$ with $y$ non-zero modulo the maximal ideal of $A$ such that $f \cdot y = x$ in $\overline{\mathbb Q}((q))$, the two power series being pushed forward along $A \to \overline{\mathbb Q}$ and included as Laurent series; (ii) every element of $A$, mapped into $F$ through the structure map from $\overline{\mathbb Q}$, lies in $W_0$; (iii) every element of the maximal ideal of $A$ maps to a non-unit of $W_0$. The proof uses neither the hypothesis that $A$ lies over $p$ nor the finiteness of the index of $\Gamma$.
--
--   This provides the Gauss valuation ring on the compositum $\overline{\mathbb Q}\cdot F(\Gamma) \subseteq \overline{\mathbb Q}((q))$ attached to a place of $\overline{\mathbb Q}$ above $p$, presented concretely by quotients of $A$-integral power series; it is the valuation-theoretic input used for reduction of the modular function field modulo $p$. It is cited in the construction of the isomorphisms of $q$-expansion function fields intertwining the Hecke and diamond operators with their reductions, and compatible with the Fricke involution.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC_of_liesOverPrime.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve
open scoped MatrixGroups

theorem ModularCurve.exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC_of_liesOverPrime
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    ∃ W₀ : ValuationSubring ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)),
      (∀ f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)), f ∈ W₀ ↔ ∃ x y : PowerSeries ↥A, y.map (IsLocalRing.residue ↥A) ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (y.map (algebraMap ↥A (AlgebraicClosure ℚ)))
          = HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (x.map (algebraMap ↥A (AlgebraicClosure ℚ)))) ∧
      (∀ a : ↥A, algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) (a : (AlgebraicClosure ℚ)) ∈ W₀) ∧
      (∀ a : ↥A, a ∈ IsLocalRing.maximalIdeal ↥A →
        algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) (a : (AlgebraicClosure ℚ)) ∈ W₀.nonunits) := by sorry
