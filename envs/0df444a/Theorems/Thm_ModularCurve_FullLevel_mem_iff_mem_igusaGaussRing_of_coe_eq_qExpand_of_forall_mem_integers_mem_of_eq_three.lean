-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_mem_iff_mem_igusaGaussRing_of_coe_eq_qExpand_of_forall_mem_integers_mem_of_eq_three
-- name    : ModularCurve.FullLevel.mem_iff_mem_igusaGaussRing_of_coe_eq_qExpand_of_forall_mem_integers_mem_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/02f837b8-4f47-5b36-9124-a8a45247db14
-- title:
--   Valuation ring meets Igusa Gauss ring on q-power expansions (q=3)
-- statement:
--   Let $q$ be a prime with $q=3$, let $M'\ge 1$ with $q\nmid M'$, and let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $q$, meaning that $q$ belongs to the nonunits of $A$. Write $F=$ `fieldBar q M'`, the intermediate field $\overline{\mathbb Q}\cdot F(\Gamma_H(q^2M'))$ of $\overline{\mathbb Q}((t))$ attached to the level group `levelH q M'`, and assume the base-changed full modular function field `modularFunctionFieldBar M'` of level $M'$ is contained in $F$. Let $R_0$ be a `ConstantReduction` of `modularFunctionFieldBar M'` over $A$ with residue field target the intermediate field of $\mathrm{ResidueField}(A)((t))$ generated over $\mathrm{ResidueField}(A)$ by `jqModC` and `jqNModC` of level $M'$; thus $R_0$ consists of a valuation subring $R_0.\mathrm{integers}$ meeting $\overline{\mathbb Q}$ exactly in $A$, a surjective residue homomorphism with kernel the maximal ideal, compatible with the residue map of $A$, a scaling property making every nonzero element representable with nonzero residue, and a place map preserving degrees and orders. It is assumed that $R_0$ is pinned to coefficientwise reduction: for every Laurent series $y$ over $A$ whose coefficientwise image in $\overline{\mathbb Q}((t))$ lies in `modularFunctionFieldBar M'`, that element lies in $R_0.\mathrm{integers}$ and its $R_0$-residue, read as a Laurent series over $\mathrm{ResidueField}(A)$, is the coefficientwise reduction of $y$. Let $O^{\mathrm{Ig}}$ be a family of valuation subrings of $F$ indexed by the projective line $\mathbb P^1(\mathbb Z/q)$, whose member at the point `lineInfty q` $=[1:0]$ is described as the Gauss ring: $f\in O^{\mathrm{Ig}}([1:0])$ if and only if there are Laurent series $x,y$ over $A$ with the coefficientwise reduction of $y$ nonzero and $f\cdot y=x$ after coefficientwise inclusion into $\overline{\mathbb Q}((t))$. Finally let $O$ be a valuation subring of $F$ whose intersection with $\overline{\mathbb Q}$ is $A$ (an element of $\overline{\mathbb Q}$ has image in $O$ exactly when it lies in $A$) and which contains the image of $R_0.\mathrm{integers}$ under the inclusion of `modularFunctionFieldBar M'` into $F$. The conclusion: for every $x\in F$ and every Laurent series $g$ over $\overline{\mathbb Q}$ lying in the intermediate field generated over $\overline{\mathbb Q}$ by the coefficientwise image of `qExpFunctionFieldC ℚ (Gamma0 M')`, if the Laurent series of $x$ is obtained from $g$ by multiplying all exponents by $q$, then $x\in O$ if and only if $x\in O^{\mathrm{Ig}}([1:0])$.
--
--   This is the $q=3$ instance of the comparison, on the subfield of $q$-power expansions of level-$\Gamma_0(M')$ functions, between an arbitrary valuation ring of the full-level field that extends the good-reduction ring of level $M'$ and the Igusa Gauss ring at the cusp $[1:0]$; the statement is the same as in the case $q\ge 5$, with $q=3$ in place of that inequality. It feeds the identification of valuation rings with Igusa rings in [`ModularCurve.FullLevel.exists_eq_igusaRing_of_forall_mem_integers_mem_of_eq_three`](thm.html#ModularCurve.FullLevel.exists_eq_igusaRing_of_forall_mem_integers_mem_of_eq_three), part of the semistable reduction analysis of modular curves at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_mem_iff_mem_igusaGaussRing_of_coe_eq_qExpand_of_forall_mem_integers_mem_of_eq_three.lean

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

theorem ModularCurve.FullLevel.mem_iff_mem_igusaGaussRing_of_coe_eq_qExpand_of_forall_mem_integers_mem_of_eq_three
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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
