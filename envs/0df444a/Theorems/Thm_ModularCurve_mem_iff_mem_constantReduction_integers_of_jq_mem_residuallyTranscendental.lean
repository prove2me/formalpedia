-- Prove2me | Theorems.Thm_ModularCurve_mem_iff_mem_constantReduction_integers_of_jq_mem_residuallyTranscendental
-- name    : ModularCurve.mem_iff_mem_constantReduction_integers_of_jq_mem_residuallyTranscendental
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/95984edc-2994-5fe1-8e9d-b80c347e240c
-- title:
--   Uniqueness of the Gauss point at level M'
-- statement:
--   Let $q$ be a prime and $M'$ a non-zero natural number with $q \nmid M'$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$, in the sense that $q$ is a non-unit of $A$, and write $\kappa = \mathrm{ResidueField}\,A$. Let $\bar L = \mathrm{modularFunctionFieldBar}\,M'$ be the subfield of $\kappa$-independent interest inside $\mathrm{LaurentSeries}\,\overline{\mathbb{Q}}$ obtained by adjoining to $\overline{\mathbb{Q}}$ the coefficientwise images of the level-$M'$ full modular function field, and let $R_0$ be a constant reduction of $A$ in $\bar L$ with residue field target $\mathrm{modularFunctionFieldC}\,\kappa\,M' = \kappa(\mathrm{jqModC}\,\kappa, \mathrm{jqNModC}\,\kappa\,M')$: thus $R_0$ provides a valuation subring $R_0.\mathrm{integers}$ of $\bar L$ meeting $\overline{\mathbb{Q}}$ exactly in $A$, a surjective residue homomorphism with kernel the maximal ideal, compatible with the residue map of $A$, together with the scaling and place-degree conditions of the structure. Assume moreover that $R_0$ is the $q$-expansion reduction: every Laurent series $y$ with coefficients in $A$ whose image in $\mathrm{LaurentSeries}\,\overline{\mathbb{Q}}$ lies in $\bar L$ lies in $R_0.\mathrm{integers}$, and its $R_0$-residue, read inside $\mathrm{LaurentSeries}\,\kappa$, is the coefficientwise reduction of $y$. Then let $V$ be any valuation subring of $\bar L$ such that (i) for $a \in \overline{\mathbb{Q}}$ one has $a \in V$ if and only if $a \in A$; (ii) the $q$-expansion $\hat\jmath$ of the modular invariant, viewed in $\bar L$, lies in $V$; (iii) for every polynomial $p$ over $\overline{\mathbb{Q}}$ with all coefficients in $A$, if $p(\hat\jmath)$ lies in the maximal ideal of $V$ then each coefficient of $p$ lies in the maximal ideal of $V$. The conclusion is that for every $f \in \bar L$, $f \in V$ if and only if $f \in R_0.\mathrm{integers}$.
--
--   This is the uniqueness of the Gauss point above $q$ on the level-$M'$ modular curve: a prolongation to the geometric modular function field of the $q$-Gauss valuation of $\overline{\mathbb{Q}}(j)$, compatible with $A$ and residually transcendental in $\hat\jmath$, coincides with the constant reduction given by $q$-expansions. It is used in the analysis of the nodes of the special fibre at full level, in the construction of node centres and the associated layered node rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_mem_iff_mem_constantReduction_integers_of_jq_mem_residuallyTranscendental.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup ModularCurve.UVCrossingModel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.mem_iff_mem_constantReduction_integers_of_jq_mem_residuallyTranscendental
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    :
    ∀ V : ValuationSubring ↥(modularFunctionFieldBar M'),
      (∀ a : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') a ∈ V ↔ a ∈ A) →
      ∀ hj : (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) ∈ V,
        (∀ p : Polynomial (AlgebraicClosure ℚ), (∀ n, p.coeff n ∈ A) →
          (∃ hm : Polynomial.aeval (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) p ∈ V, (⟨_, hm⟩ : ↥V) ∈ maximalIdeal ↥V) →
            ∀ n, ∃ hc : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (p.coeff n) ∈ V, (⟨_, hc⟩ : ↥V) ∈ maximalIdeal ↥V) →
        ∀ f : ↥(modularFunctionFieldBar M'), f ∈ V ↔ f ∈ R₀.integers := by sorry
