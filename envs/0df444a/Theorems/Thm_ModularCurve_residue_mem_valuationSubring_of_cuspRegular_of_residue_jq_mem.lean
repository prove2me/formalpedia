-- Prove2me | Theorems.Thm_ModularCurve_residue_mem_valuationSubring_of_cuspRegular_of_residue_jq_mem
-- name    : ModularCurve.residue_mem_valuationSubring_of_cuspRegular_of_residue_jq_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/6b711c56-5307-502e-92f6-e41b866459c6
-- title:
--   Reduction of a cusp-regular integral function stays regular
-- statement:
--   Fix a prime $q$ and a positive integer $M'$ with $q \nmid M'$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$ in the sense that $q$ is a non-unit of $A$; write $\kappa =$ `ResidueField A`. Let $F =$ `modularFunctionFieldBar M'` be the base change to $\overline{\mathbb{Q}}$, inside $\overline{\mathbb{Q}}((q))$, of the full level-$M'$ modular function field, and let $\bar F =$ `modularFunctionFieldC κ M'` be the subfield of $\kappa((q))$ generated over $\kappa$ by `jqModC κ` and `jqNModC κ M'`. Let $R_0$ be a constant reduction of $F$ along $A$ with values in $\bar F$, i.e. a valuation subring `R₀.integers` of $F$ together with a surjective residue homomorphism onto $\bar F$ with kernel the maximal ideal, compatible with $A$ on constants and with a push-forward map on places satisfying the degree and divisor axioms. Assume $R_0$ is computed coefficientwise: for every Laurent series $y$ over $A$ whose coefficientwise image in $\overline{\mathbb{Q}}((q))$ lies in $F$, that element is $R_0$-integral and its residue, read inside $\kappa((q))$, is the coefficientwise reduction of $y$. Let $x \in F$ be $R_0$-integral, and assume $x$ is regular at every place $P$ of $F/\overline{\mathbb{Q}}$ at which the image $j$ of `jq` under coefficientwise extension of scalars is regular, i.e. $0 \le P.\mathrm{ord}(j)$ implies $0 \le P.\mathrm{ord}(x)$. Assume also that $j$ is $R_0$-integral. Then for every place $v$ of $\bar F/\kappa$ at which the residue of $j$ lies in the valuation subring of $v$, the residue of $x$ lies in the valuation subring of $v$.
--
--   This is the Deuring-style statement that constant reduction preserves regularity away from the cusps: the pole divisor of the reduction of $j$ is the push-forward of the pole divisor of $j$, so a function regular off the cusps of $X_0(M')$ reduces to a function regular wherever $\bar j$ is. It is the geometric input to [`ModularCurve.exists_sum_smul_coeffEmb_of_mem_integers_of_cuspRegular`](thm.html#ModularCurve.exists_sum_smul_coeffEmb_of_mem_integers_of_cuspRegular), which expresses $A$-integral cusp-regular functions as $A$-combinations of rational ones.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_residue_mem_valuationSubring_of_cuspRegular_of_residue_jq_mem.lean

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

theorem ModularCurve.residue_mem_valuationSubring_of_cuspRegular_of_residue_jq_mem
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (x : ↥(modularFunctionFieldBar M')) (hx : x ∈ R₀.integers)
    (hreg : ∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
      0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord x)
    (hj : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) ∈ R₀.integers)
    (v : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))
    (hv : (R₀.residue ⟨_, hj⟩ : modularFunctionFieldC (ResidueField A) M') ∈ v.toValuationSubring) :
    (R₀.residue ⟨x, hx⟩ : modularFunctionFieldC (ResidueField A) M') ∈ v.toValuationSubring := by sorry
