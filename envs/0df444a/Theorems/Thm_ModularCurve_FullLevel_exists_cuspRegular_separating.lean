-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_cuspRegular_separating
-- name    : ModularCurve.FullLevel.exists_cuspRegular_separating
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/56fca188-f9be-51b8-9175-a4fa221ebb62
-- title:
--   Separating supersingular places by reductions of cusp-regular integral functions
-- statement:
--   Fix a prime $q$ and a nonzero natural number $M'$ with $q \nmid M'$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ lying over $q$ in the sense that the image of $q$ lies in the nonunits of $A$. Let $\kappa = \mathrm{ResidueField}\,A$ and let $R_0$ be a `ConstantReduction` of $A$ from $\overline{\mathbb{Q}}$-base-changed full level-$M'$ modular function field `modularFunctionFieldBar M'` to `modularFunctionFieldC κ M'` $=\kappa(\mathrm{jqModC}, \mathrm{jqNModC})$: that is, a valuation subring $R_0.\mathrm{integers}$ of the former, a surjective residue homomorphism onto the latter with kernel the maximal ideal, and a degree-preserving map on places, compatible with the structure maps as in the definition. Assume $R_0$ is pinned to coefficientwise reduction: for every Laurent series $y$ over $A$ whose coefficientwise image in $\mathrm{LaurentSeries}\,\overline{\mathbb{Q}}$ lies in `modularFunctionFieldBar M'`, that element belongs to $R_0.\mathrm{integers}$ and its $R_0$-residue, read as a Laurent series over $\kappa$, is the coefficientwise residue of $y$. Let $W$ be a finite set of places of `modularFunctionFieldC κ M'` over $\kappa$ whose members are exactly the places satisfying `IsSupersingularPlace q M' κ`. Then for any two distinct $s, s' \in W$ there are an element $f$ of `modularFunctionFieldBar M'` and a proof that $f \in R_0.\mathrm{integers}$ such that: at every place $P$ of `modularFunctionFieldBar M'` over $\overline{\mathbb{Q}}$ at which the coefficient-embedded $q$-expansion `jq` of $j$ has nonnegative order, $f$ also has nonnegative order; the residue $R_0.\mathrm{residue}\,f$ lies in the valuation subrings of both $s$ and $s'$; and its evaluations `evalAt` at $s$ and at $s'$ differ.
--
--   This is the statement that the supersingular points of the reduction of the level-$M'$ modular curve are separated by reductions of cusp-regular $R_0$-integral modular functions, the residue of $R_0$ carrying such functions onto the affine coordinate ring of the good reduction of $Y_0(M')$ over $\kappa$. It supplies, in exactly the shape required, the separation hypothesis used by the existence results for semistable coverings of the full-level modular curve at a prime dividing the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_cuspRegular_separating.lean

import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.exists_cuspRegular_separating
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A)) :
    ∀ s s' : ↥W, s ≠ s' → ∃ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) ∧
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ∧
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s' : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ∧
      (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) ≠
        (s' : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) := by sorry
