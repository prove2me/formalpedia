-- Prove2me | Theorems.Thm_ModularCurve_algebraMap_coeff_mem_of_mem_integers_of_cuspRegular
-- name    : ModularCurve.algebraMap_coeff_mem_of_mem_integers_of_cuspRegular
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/21ccfb4e-e940-5293-84d8-1cc76cccf47f
-- title:
--   Integrality of q-coefficients for cusp-regular modular functions
-- statement:
--   Fix a prime $q$ and an integer $M'\ge 1$, and let $A$ be a valuation subring of $\overline{\mathbb Q}=\mathrm{AlgebraicClosure}\ \mathbb Q$ lying over $q$ in the sense that $q$, viewed in $\overline{\mathbb Q}$, belongs to `A.nonunits`. Let $R_0$ be a `ConstantReduction` for $A$ from the field $\overline{\mathbb Q}\bigl(\!(q)\!\bigr)$-subfield `modularFunctionFieldBar M'`, the base change to $\overline{\mathbb Q}$ of the level-$M'$ field `modularFunctionFieldFull M'` $=\mathbb Q(\mathrm{divisorExpansions}\ M')$ inside $\mathbb Q(\!(q)\!)$, to the field `modularFunctionFieldC (ResidueField A) M'` obtained by adjoining the mod-reduced expansions `jqModC` and `jqNModC` to the residue field of $A$; thus $R_0$ consists of a valuation subring `R₀.integers`, a surjective residue map onto the target with kernel the maximal ideal, a map on places preserving degrees and orders, and the compatibility with $A$ recorded in the structure. Assume further that $R_0$ computes coefficientwise reduction: for every Laurent series $y$ over $A$ whose image in $\overline{\mathbb Q}(\!(q)\!)$ lies in `modularFunctionFieldBar M'`, that element lies in `R₀.integers` and its $R_0$-residue, read as a Laurent series over the residue field of $A$, is the coefficientwise reduction of $y$. Let $g\in\mathbb Q(\!(q)\!)$ lie in `modularFunctionFieldFull M'`, suppose its coefficientwise image in $\overline{\mathbb Q}(\!(q)\!)$ lies in `R₀.integers`, and suppose $g$ is cusp-regular: for every place $P$ of `modularFunctionFieldBar M'` over $\overline{\mathbb Q}$, if $\mathrm{ord}_P$ of the image of the expansion `jq` is $\ge 0$ then so is $\mathrm{ord}_P$ of the image of $g$. Then for every $n\in\mathbb Z$ the image of the $n$-th coefficient $g_n$ in $\overline{\mathbb Q}$ lies in $A$.
--
--   This is the integrality (bounded-denominators) half of the $q$-expansion dictionary for rational modular functions of level $M'$: integrality of an element for the Gauss-type reduction $R_0$, together with regularity at the cusps where $j$ is regular, forces every Fourier coefficient to be $A$-integral, with no auxiliary denominator. It feeds the chart-membership statements used to produce algebra homomorphisms matching $q$-expansions with their reductions at semistable places, in particular the full-level and Diamond-style specialisation results.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_algebraMap_coeff_mem_of_mem_integers_of_cuspRegular.lean

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

theorem ModularCurve.algebraMap_coeff_mem_of_mem_integers_of_cuspRegular
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
    (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ :
        ↥(modularFunctionFieldBar M')) ∈ R₀.integers)
    (hcusp : ∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M'))) :
    ∀ n : ℤ, algebraMap ℚ (AlgebraicClosure ℚ) (g.coeff n) ∈ A := by sorry
