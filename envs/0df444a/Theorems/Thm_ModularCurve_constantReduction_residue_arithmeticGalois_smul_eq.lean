-- Prove2me | Theorems.Thm_ModularCurve_constantReduction_residue_arithmeticGalois_smul_eq
-- name    : ModularCurve.constantReduction_residue_arithmeticGalois_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/09afb259-a5bc-5ab2-b28b-b54b128983f0
-- title:
--   Inertia acts trivially on a pinned constant reduction
-- statement:
--   Fix a prime $q$ with $q \ge 5$ and a nonzero natural number $M'$ not divisible by $q$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$ in the sense that $q$ is a nonunit of $A$; write $\kappa =$ `ResidueField A`. Let $R_0$ be a constant reduction, in the sense of `ConstantReduction`, of the field $\overline{\mathbb{Q}} \cdot F(\Gamma_0(M'))$ — that is, of `modularFunctionFieldBar M'`, the base change to $\overline{\mathbb{Q}}$ inside $\overline{\mathbb{Q}}((q))$ of the level-$M'$ modular function field `modularFunctionFieldFull M'` — along $A$, with residue field target `modularFunctionFieldC κ M'`, the subfield of $\kappa((q))$ generated over $\kappa$ by the reductions of the $q$-expansions of $j$ and $j(M' \cdot)$; so $R_0$ consists of a valuation subring of integers inducing $A$ on $\overline{\mathbb{Q}}$, a surjective residue homomorphism with kernel the maximal ideal, compatibility with $A \to \kappa$ on constants, a scaling property making every nonzero element a constant multiple of one with nonzero residue, and a degree- and order-preserving map on places. Assume $R_0$ is pinned coefficientwise: for every Laurent series $y$ with coefficients in $A$ whose image in $\overline{\mathbb{Q}}((q))$ lies in `modularFunctionFieldBar M'`, that image is $R_0$-integral and its $R_0$-residue, viewed in $\kappa((q))$, is the coefficientwise reduction of $y$. The conclusion: for every $\tau$ in the image in $\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ (i.e. `A.inertiaSubgroupIn ℚ`) and every $R_0$-integral $f$, the element $\tau \cdot f$ obtained by letting $\tau$ act coefficientwise on $q$-expansions, via `arithmeticGalois (modularFunctionFieldFull M')`, is again $R_0$-integral and has the same $R_0$-residue as $f$.
--
--   This is the $q$-expansion form of the statement that inertia at $q$ acts trivially on the good (constant) reduction of the level-$M'$ modular function field, the reduction being pinned by the requirement that integral $q$-expansions reduce coefficientwise. It is used in the analysis of the Galois action on the Drinfeld-type ring of the reduced curve, through [`ModularCurve.FullLevel.arithmeticGalois_smul_mem_drinfeldRing_iff_of_componentChart`](thm.html#ModularCurve.FullLevel.arithmeticGalois_smul_mem_drinfeldRing_iff_of_componentChart); the proof cites the representation of a nonzero element as a quotient of two series with $A$-integral expansions of nonzero reduction, together with the identification of the $q$-expansion field of $\Gamma_0(M')$ over $\mathbb{Q}$ with `modularFunctionFieldFull M'`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_constantReduction_residue_arithmeticGalois_smul_eq.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
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

theorem ModularCurve.constantReduction_residue_arithmeticGalois_smul_eq
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y) :
    ∀ τ ∈ A.inertiaSubgroupIn ℚ, ∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      ∃ hf' : ModularCurve.arithmeticGalois (modularFunctionFieldFull M') τ • f ∈ R₀.integers, R₀.residue ⟨ModularCurve.arithmeticGalois (modularFunctionFieldFull M') τ • f, hf'⟩ = R₀.residue ⟨f, hf⟩ := by sorry
