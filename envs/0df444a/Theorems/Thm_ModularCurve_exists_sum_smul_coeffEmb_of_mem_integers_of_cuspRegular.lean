-- Prove2me | Theorems.Thm_ModularCurve_exists_sum_smul_coeffEmb_of_mem_integers_of_cuspRegular
-- name    : ModularCurve.exists_sum_smul_coeffEmb_of_mem_integers_of_cuspRegular
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/03183dc2-1cd8-5c2a-a221-55dd28ae7cea
-- title:
--   Cusp-regular Gauss-integral functions as A-combinations of rational ones
-- statement:
--   Let $q$ be a prime, $M'$ a nonzero natural number with $q \nmid M'$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$ in the sense that $q$ is a nonunit of $A$. Write $F =$ `modularFunctionFieldBar M'` for the base change to $\overline{\mathbb{Q}}$-coefficients of the level-$M'$ modular function field `modularFunctionFieldFull M'` $\subset \overline{\mathbb{Q}}((q))$-expansions, and let $R_0$ be a `ConstantReduction` of $A$ on $F$ with values in `modularFunctionFieldC (ResidueField A) M'`, i.e. a valuation subring $R_0.\mathrm{integers}$ of $F$ together with a surjective ring map `R₀.residue` onto that field whose kernel is the maximal ideal, a map on places preserving degrees and compatible with orders, and the compatibilities with $A$ and its residue map recorded in the structure. It is assumed that $R_0$ is the coefficientwise (Gauss) reduction: for every Laurent series $y$ over $A$ whose coefficientwise image lies in $F$, that image lies in $R_0.\mathrm{integers}$ and its residue, read as a Laurent series over the residue field of $A$, is the coefficientwise reduction of $y$. Let $f \in F$ lie in $R_0.\mathrm{integers}$ and be regular wherever $j$ is: for every place $P$ of $F$ over $\overline{\mathbb{Q}}$ (a proper valuation subring containing $\overline{\mathbb{Q}}$ whose ring is a principal ideal ring), $P.\mathrm{ord}$ of the image of the $q$-expansion `jq` being $\ge 0$ forces $P.\mathrm{ord}(f) \ge 0$. Then there are $n \in \mathbb{N}$, constants $a_i \in A$ and Laurent series $g_i$ over $\mathbb{Q}$ lying in `modularFunctionFieldFull M'` such that each image $\mathrm{coeffEmb}(g_i)$ lies in $R_0.\mathrm{integers}$, each is regular at every place where the image of `jq` is, the image of `jq` itself lies in $R_0.\mathrm{integers}$ and for each $i$ every place $v$ of `modularFunctionFieldC (ResidueField A) M'` over the residue field of $A$ whose valuation subring contains the residue of `jq` also contains the residue of $\mathrm{coeffEmb}(g_i)$, and finally $f = \sum_i a_i \cdot \mathrm{coeffEmb}(g_i)$, the $a_i$ acting through $\overline{\mathbb{Q}} \to F$.
--
--   This is a denominator-free form of the statement that, at a place of good reduction, the Gauss-integral functions on $X(M')_{\overline{\mathbb{Q}}}$ that are regular away from the cusps are spanned over $A$ by functions with rational $q$-expansions, with the regularity of the reductions relative to that of the reduction of $j$ preserved; it is the function-field shadow of the $q$-expansion principle. It is used in the construction of rational integral cusp-regular functions with prescribed values and in the construction of regular prolongations and smooth-point charts for the full-level modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_sum_smul_coeffEmb_of_mem_integers_of_cuspRegular.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
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

theorem ModularCurve.exists_sum_smul_coeffEmb_of_mem_integers_of_cuspRegular
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers)
    (hreg : ∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
      0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) :
    ∃ (n : ℕ) (a : Fin n → A) (g : Fin n → LaurentSeries ℚ) (hg : ∀ i, g i ∈ modularFunctionFieldFull M'),
      (∀ i, (⟨coeffEmb (AlgebraicClosure ℚ) (g i), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (hg i)⟩ :
          ↥(modularFunctionFieldBar M')) ∈ R₀.integers) ∧
      (∀ i, ∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (g i), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (hg i)⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M'))) ∧
      (∃ hj : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ∀ i (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) (g i), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (hg i)⟩ :
            ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
          ∀ v : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'),
            (R₀.residue ⟨_, hj⟩ : modularFunctionFieldC (ResidueField A) M') ∈ v.toValuationSubring →
            (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈ v.toValuationSubring) ∧
      (f : ↥(modularFunctionFieldBar M')) =
        ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (a i : AlgebraicClosure ℚ) *
          (⟨coeffEmb (AlgebraicClosure ℚ) (g i), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (hg i)⟩ :
            ↥(modularFunctionFieldBar M')) := by sorry
