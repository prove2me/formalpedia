-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_ssTube_of_residue_evalAt_mem_ssJSet_of_eq_two
-- name    : ModularCurve.FullLevel.exists_ssTube_of_residue_evalAt_mem_ssJSet_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/bef6c162-58c8-56c7-ae00-2957b2d214ad
-- title:
--   Supersingular reduction puts a rational place in a supersingular tube (q=2)
-- statement:
--   Let $q$ be a prime with $q=2$, let $M'$ be a nonzero natural number not divisible by $q$, and let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $q$ in the sense that $q$ belongs to the nonunits of $A$; write $\kappa=\mathrm{ResidueField}\,A$. Let $W$ be a finite set of places of the field $\mathrm{modularFunctionFieldC}\,\kappa\,M'=\kappa(j_{\mathsf q},j_{\mathsf q,M'})$ over $\kappa$ whose members are exactly the places satisfying `IsSupersingularPlace` for $q$ and $M'$, let $\mathrm{hle}$ be an inclusion of the base-changed full level-$M'$ Laurent-series field $\mathrm{modularFunctionFieldBar}\,M'$ into $\mathrm{fieldBar}\,q\,M'=\mathrm{xHFunctionFieldBar}(q^2M')(\mathrm{levelH}\,q\,M')$, and let $R_0$ be a constant reduction of $\mathrm{modularFunctionFieldBar}\,M'$ at $A$ with values in $\mathrm{modularFunctionFieldC}\,\kappa\,M'$: a valuation subring $R_0.\mathrm{integers}$, a surjective ring map $R_0.\mathrm{residue}$ onto that field with kernel the maximal ideal, agreeing with $A$ under $\overline{\mathbb Q}\to F$ and with reduction of constants, together with a place map preserving degrees and pole divisors. Assume the $\mathsf q$-expansion compatibility $\mathrm{hR}_0$: every Laurent series $y$ over $A$ whose coefficientwise image in $\mathrm{LaurentSeries}\,\overline{\mathbb Q}$ lies in $\mathrm{modularFunctionFieldBar}\,M'$ lies in $R_0.\mathrm{integers}$, and its residue, read as a Laurent series over $\kappa$, is the coefficientwise reduction of $y$. Then for every place $P$ of $\mathrm{fieldBar}\,q\,M'$ over $\overline{\mathbb Q}$ that is rational (the structure map $\overline{\mathbb Q}\to$ residue field of $P$ is surjective), such that the image $j$ of the coefficientwise embedding of $j_{\mathsf q}$ lies in the valuation subring of $P$, such that $P.\mathrm{evalAt}\,j$ lies in $A$, and such that the reduction of $P.\mathrm{evalAt}\,j$ in $\kappa$ lies in $\mathrm{ssJSet}\,q\,\kappa$ (every elliptic curve over $\kappa$ with that $j$-invariant has no nonzero point killed by $q$), there exists $s\in W$ with the following property: for every $f\in R_0.\mathrm{integers}$ which has no pole at any place of $\mathrm{modularFunctionFieldBar}\,M'$ where $j$ has none, and whose residue $R_0.\mathrm{residue}\,f$ lies in the valuation subring of $s$, and for every $a\in A$ whose reduction equals $s.\mathrm{evalAt}(R_0.\mathrm{residue}\,f)$, the difference $P.\mathrm{evalAt}(\mathrm{hle}(f))-a$ lies in $A$ and in fact in the maximal ideal of $A$.
--
--   This is the Deuring-type statement that a $\overline{\mathbb Q}$-rational place of the level-$q^2M'$ field at which the modular invariant is regular, $A$-integral and supersingular modulo the maximal ideal of $A$ lies in the $A$-adic tube of a supersingular place of the level-$M'$ curve in characteristic $q$, here in the case $q=2$. It feeds the statement [`ModularCurve.FullLevel.map_jChartFin_not_mem_ssJSet_of_centred_of_forall_not_ssTube_twoChartIntegralModel_of_eq_two`](thm.html#ModularCurve.FullLevel.map_jChartFin_not_mem_ssJSet_of_centred_of_forall_not_ssTube_twoChartIntegralModel_of_eq_two), a step in the construction of a semistable covering of the modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_ssTube_of_residue_evalAt_mem_ssJSet_of_eq_two.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open ModularCurve
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.FullLevel.exists_ssTube_of_residue_evalAt_mem_ssJSet_of_eq_two
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y) :

    ∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P.IsRational →
      ∀ (hjP : (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) ∈ P.toValuationSubring) (hjA : P.evalAt (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) ∈ A),
        IsLocalRing.residue ↥A ⟨_, hjA⟩ ∈ ModularCurve.ssJSet q (ResidueField ↥A) →
      ∃ s : ↥W, ∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
                (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
                  0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                    ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
                (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                    (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
                  ∀ a : A, residue A a =
                      (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
                    ∃ h : P.evalAt (IntermediateField.inclusion hle f : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
                      (⟨_, h⟩ : A) ∈ maximalIdeal A := by sorry
