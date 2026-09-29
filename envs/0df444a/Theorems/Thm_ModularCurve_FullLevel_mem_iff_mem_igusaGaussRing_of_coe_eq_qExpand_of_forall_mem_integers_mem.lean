-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_mem_iff_mem_igusaGaussRing_of_coe_eq_qExpand_of_forall_mem_integers_mem
-- name    : ModularCurve.FullLevel.mem_iff_mem_igusaGaussRing_of_coe_eq_qExpand_of_forall_mem_integers_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/d6386ce0-605a-5621-9b38-c3f02625cd12
-- title:
--   Valuation ring agrees with the Igusa Gauss ring on q-scaled functions
-- statement:
--   Fix a prime $q \ge 5$ and $M' \ge 1$ with $q \nmid M'$, and a valuation subring $A$ of an algebraic closure $\overline{\mathbb{Q}}$ of $\mathbb{Q}$ such that the image of $q$ is a non-unit of $A$. Assume the level-$M'$ field $F_{M'} =$ `modularFunctionFieldBar M'` (the subfield of $\overline{\mathbb{Q}}(\!(q)\!)$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of `modularFunctionFieldFull M'`) is contained in $F =$ `fieldBar q M'` $=$ `xHFunctionFieldBar (q^2 * M') (levelH q M')`. Let $R_0$ be a `ConstantReduction` of $F_{M'}$ along $A$ with residue field target `modularFunctionFieldC (ResidueField A) M'`: a valuation subring $R_0.\mathrm{integers}$ of $F_{M'}$ together with a surjective homomorphism onto that field with kernel the maximal ideal, agreeing with $A$ on constants, reducing constants via $A \to \kappa(A)$, admitting scalings to non-zero residue, and carrying places degree- and order-compatibly; assume moreover that every Laurent series $y$ over $A$ whose image in $\overline{\mathbb{Q}}(\!(q)\!)$ lies in $F_{M'}$ lies in $R_0.\mathrm{integers}$ with residue the coefficientwise reduction of $y$. Let $O^{\mathrm{Ig}}$ be a family of valuation subrings of $F$ indexed by $\mathbb{P}^1(\mathbb{Z}/q)$ whose member at the point $[1:0] =$ `lineInfty q` consists exactly of those $f$ with $f\,\bar y = \bar x$ for some Laurent series $x,y$ over $A$ with the coefficientwise reduction of $y$ non-zero. Let $O$ be a valuation subring of $F$ with $O \cap \overline{\mathbb{Q}} = A$ and $R_0.\mathrm{integers} \subseteq O$. Then for every $x \in F$ whose $q$-expansion is `qExpand` of some $g$ in the subfield of $\overline{\mathbb{Q}}(\!(q)\!)$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of `qExpFunctionFieldC ℚ (Gamma0 M')`, that is, $g$ with all exponents multiplied by $q$, one has $x \in O$ if and only if $x \in O^{\mathrm{Ig}}([1:0])$. Only the value of $O^{\mathrm{Ig}}$ at $[1:0]$ enters.
--
--   This is the comparison step showing that any valuation ring of the full-level field lying over $A$ and dominating the good reduction of the level-$M'$ field coincides with the Igusa Gauss ring on the subfield of functions $g(qz)$, which is the function field of $X_0(M')$ in the $q$-scaled embedding; it rests on the uniqueness of a regular prolongation with full residue degree over the $j(qz)$-line. It is used in the identification of such a valuation ring with the Igusa ring at the cusp $[1:0]$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_mem_iff_mem_igusaGaussRing_of_coe_eq_qExpand_of_forall_mem_integers_mem.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.mem_iff_mem_igusaGaussRing_of_coe_eq_qExpand_of_forall_mem_integers_mem
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (O : ValuationSubring (fieldBar q M'))
    (hOA : ∀ x : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ O ↔ x ∈ A)
    (hOR₀ : ∀ f : ↥(modularFunctionFieldBar M'), f ∈ R₀.integers →
      (IntermediateField.inclusion hle f : fieldBar q M') ∈ O)
    (x : fieldBar q M') (g : LaurentSeries (AlgebraicClosure ℚ))
    (hg : g ∈ laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')))
    (hx : (x : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) q g) :
    x ∈ O ↔ x ∈ OIg (lineInfty q) := by sorry
