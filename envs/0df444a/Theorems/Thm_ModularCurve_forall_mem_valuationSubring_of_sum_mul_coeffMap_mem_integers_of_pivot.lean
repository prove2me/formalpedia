-- Prove2me | Theorems.Thm_ModularCurve_forall_mem_valuationSubring_of_sum_mul_coeffMap_mem_integers_of_pivot
-- name    : ModularCurve.forall_mem_valuationSubring_of_sum_mul_coeffMap_mem_integers_of_pivot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/06e5e1e7-5c33-55a8-a5ae-989684353ce9
-- title:
--   Pivot families force integral coordinates under constant reduction
-- statement:
--   Fix a positive natural number $M'$ and a valuation subring $A$ of $\overline{\mathbb{Q}}$, and let $R_0$ be a constant reduction of $A$ on the field $F = \overline{\mathbb{Q}}(\mathrm{modularFunctionFieldFull}\,M')$, generated over $\overline{\mathbb{Q}}$ inside $\overline{\mathbb{Q}}((q))$ by the coefficientwise image of the full level-$M'$ modular function field, with values in the subfield of $\kappa((q))$ generated over the residue field $\kappa$ of $A$ by $j(q)$ and $j(q^{M'})$; so $R_0$ consists of a valuation subring $\mathcal{O}_{R_0}$ of $F$, a surjective ring map from it onto that subfield with kernel its maximal ideal, a map on places, and the usual compatibilities with $A$. Assume that for each Laurent series $y$ with coefficients in $A$ whose image in $\overline{\mathbb{Q}}((q))$ lies in $F$, this image lies in $\mathcal{O}_{R_0}$ and its $R_0$-residue, read as a Laurent series over $\kappa$, is the coefficientwise reduction of $y$. Let $c_i \in \overline{\mathbb{Q}}$ and $y_i$ ($i \in \mathrm{Fin}\,n$) be Laurent series over $A$ whose images lie in $F$, and let $p_i \in \mathbb{Z}$ satisfy $\mathrm{coeff}_{p_i}(y_j) = \delta_{ij}$. If $\sum_i c_i y_i \in \mathcal{O}_{R_0}$, then $c_i \in A$ for every $i$.
--
--   This is the integrality half of a $q$-expansion principle: membership in the integers of a constant reduction of a modular function field is detected on coefficients, so that a family of $A$-integral $q$-expansions in pivot (echelon) position has $A$-integral coordinates. It is used, via a pivot basis of a Riemann–Roch space attached to a cuspidal divisor, to write Gauss-integral cusp-regular level-$M'$ functions as $A$-combinations of rational ones, in [`ModularCurve.exists_sum_smul_coeffEmb_of_mem_integers_of_cuspRegular`](thm.html#ModularCurve.exists_sum_smul_coeffEmb_of_mem_integers_of_cuspRegular).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_forall_mem_valuationSubring_of_sum_mul_coeffMap_mem_integers_of_pivot.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.forall_mem_valuationSubring_of_sum_mul_coeffMap_mem_integers_of_pivot
    (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    {n : ℕ} (c : Fin n → AlgebraicClosure ℚ) (y : Fin n → LaurentSeries ↥A)
    (hy : ∀ i, coeffMap A.subtype (y i) ∈ modularFunctionFieldBar M')
    (p : Fin n → ℤ) (hpiv : ∀ i j, (y j).coeff (p i) = if i = j then 1 else 0)
    (hf : (∑ i, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (c i) *
        (⟨coeffMap A.subtype (y i), hy i⟩ : ↥(modularFunctionFieldBar M'))) ∈ R₀.integers) :
    ∀ i, c i ∈ A := by sorry
