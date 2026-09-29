-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_ComponentChart_exists_residue_inclusion_eq_algebraMap_evalAt_of_integers_eq
-- name    : ModularCurve.FullLevel.ComponentChart.exists_residue_inclusion_eq_algebraMap_evalAt_of_integers_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/2b70bf6d-5a5b-58dc-bd2c-e89bd38032d8
-- title:
--   Chart residue of a level function equals its value at s
-- statement:
--   Fix a prime $q$ and a nonzero natural number $M'$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, and a finite set $W$ of places (in the sense of the structure `Place`: valuation subrings of the ambient field that contain the image of the base field, are proper and are principal ideal rings) of the field $\mathrm{modularFunctionFieldC}\,(\mathrm{ResidueField}\,A)\,M'$, the subfield of $\mathrm{LaurentSeries}(\mathrm{ResidueField}\,A)$ generated over the residue field of $A$ by the two reduced $q$-expansions $jq$ and $jq_{N}$. Assume an inclusion $\mathrm{hle}$ of $\mathrm{modularFunctionFieldBar}\,M'$ (the base change to $\overline{\mathbb{Q}}$ of the full level-$M'$ modular function field) into $\mathrm{fieldBar}\,q\,M' = \mathrm{xHFunctionFieldBar}\,(q^2M')\,(\mathrm{levelH}\,q\,M')$, and let $R_0$ be a constant reduction of $A$ on $\mathrm{modularFunctionFieldBar}\,M'$ with values in $\mathrm{modularFunctionFieldC}\,(\mathrm{ResidueField}\,A)\,M'$, that is: a valuation subring $R_0.\mathrm{integers}$ on which the constants of $A$ are exactly the integral ones, a surjective residue homomorphism with kernel the maximal ideal and extending the residue map of $A$, a scaling property making every nonzero function have nonzero reduction after multiplication by a constant, and a degree-preserving map on places compatible with pushforward of divisors. Let $OSS$ assign to each $s \in W$ a valuation subring of $\mathrm{fieldBar}\,q\,M'$, subject to the hypothesis $\mathrm{hSS\_over}$: for every $s\in W$ and every $f$ in $R_0.\mathrm{integers}$ which is regular wherever the element $jq$ of $\mathrm{modularFunctionFieldBar}\,M'$ (the image of the Laurent series $jq$ under $\mathrm{coeffEmb}$) is regular, i.e. $\mathrm{ord}_P(f)\ge 0$ at every place $P$ of $\mathrm{modularFunctionFieldBar}\,M'$ over $\overline{\mathbb{Q}}$ with $\mathrm{ord}_P(jq)\ge 0$, and whose reduction $R_0.\mathrm{residue}(f)$ lies in the valuation subring of $s$, the image of $f$ in $\mathrm{fieldBar}\,q\,M'$ lies in $OSS\,s$ and, for every $a\in A$ whose residue equals $s.\mathrm{evalAt}(R_0.\mathrm{residue}(f))$ (the value of the reduction at $s$, computed through the inverse of the residue map of $s$ on its residue field), the difference of that image and the image of $a$ lies in the maximal ideal of $OSS\,s$. Then, given $s\in W$, a field $FSS$ over $\mathrm{ResidueField}\,A$, a component chart $C$ for $A$ on $\mathrm{fieldBar}\,q\,M'$ with residues in $FSS$ whose ring of integers is $OSS\,s$, and an $f$ in $R_0.\mathrm{integers}$ satisfying the same regularity condition off the zeros of $jq$ and with $R_0.\mathrm{residue}(f)$ in the valuation subring of $s$: the image of $f$ in $\mathrm{fieldBar}\,q\,M'$ lies in $C.\mathrm{integers}$, and its residue under $C$ is the image in $FSS$ of $s.\mathrm{evalAt}(R_0.\mathrm{residue}(f))$.
--
--   This is a bookkeeping step in the construction of a semistable covering of the full-level modular curve: it transfers the characterising property of the valuation ring attached to a place $s$ (here the data $\mathrm{hSS\_over}$) into the statement that the component chart sitting over $s$ sends a level function to the constant given by the value of its reduction at $s$. It is used by the three assembly results producing semistable coverings of $X(\Gamma_H(q^2M'))$ together with their equivalence clauses.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_ComponentChart_exists_residue_inclusion_eq_algebraMap_evalAt_of_integers_eq.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCoveringNaturality
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringGuards
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.FullLevel.ComponentChart.exists_residue_inclusion_eq_algebraMap_evalAt_of_integers_eq
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (OSS : ↥W → ValuationSubring (fieldBar q M'))
    (hSS_over : ∀ (s : ↥W) (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle f : fieldBar q M') ∈ OSS s ∧
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
          ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
              - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s,
            (⟨_, h⟩ : OSS s) ∈ maximalIdeal (OSS s))
    (s : ↥W) {FSS : Type} [Field FSS] [Algebra (ResidueField A) FSS]
    (C : ComponentChart A (fieldBar q M') FSS) (hCint : C.integers = OSS s)
    (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers)
    (hreg : ∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M')))
    (hs : (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring) :
    ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ C.integers,
      C.residue ⟨_, hC⟩ = algebraMap (ResidueField A) FSS
        ((s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩)) := by sorry
