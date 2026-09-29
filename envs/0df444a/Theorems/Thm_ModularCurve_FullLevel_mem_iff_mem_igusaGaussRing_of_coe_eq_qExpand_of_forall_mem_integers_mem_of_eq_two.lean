-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_mem_iff_mem_igusaGaussRing_of_coe_eq_qExpand_of_forall_mem_integers_mem_of_eq_two
-- name    : ModularCurve.FullLevel.mem_iff_mem_igusaGaussRing_of_coe_eq_qExpand_of_forall_mem_integers_mem_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/4c674cca-3b31-5cac-9a24-ba0c703f8d7d
-- title:
--   Case q=2: 𝒪 agrees with the Igusa ring on q^q-expansions
-- statement:
--   Fix a prime $q$ with $q=2$ and an integer $M'\neq 0$ with $q\nmid M'$; let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$. Write $F_{M'}=$ `modularFunctionFieldBar M'`, the $\overline{\mathbb Q}$-base change inside $\overline{\mathbb Q}(\!(q)\!)$ of the full level-$M'$ modular function field, and $F=$ `fieldBar q M'` $=$ `xHFunctionFieldBar (q ^ 2 * M') (levelH q M')`, and assume $F_{M'}\le F$. Let $R_0$ be a constant reduction of $F_{M'}$ along $A$ with values in `modularFunctionFieldC (ResidueField A) M'` — so a valuation subring $R_0.\mathrm{integers}$ of $F_{M'}$, a surjective residue homomorphism with kernel the maximal ideal, a degree-preserving map on places compatible with divisors, and the constants of $A$ reducing as in $A$ — and assume $R_0$ is pinned to coefficientwise reduction: every Laurent series $y$ over $A$ whose image in $\overline{\mathbb Q}(\!(q)\!)$ lies in $F_{M'}$ is $R_0$-integral, with residue the coefficientwise reduction of $y$. Let $O^{\mathrm{Ig}}$ be a family of valuation subrings of $F$ indexed by $\mathbb P^1(\mathbb Z/q)$ whose value at the point $[1:0]$ is the Gauss ring: $f$ belongs to it exactly when $f\cdot \bar y=\bar x$ for some Laurent series $x,y$ over $A$ with $y$ having nonzero coefficientwise reduction. Let $O$ be a valuation subring of $F$ with $O\cap\overline{\mathbb Q}=A$ and with the image of $R_0.\mathrm{integers}$ under the inclusion $F_{M'}\le F$ contained in $O$. Then for every $x\in F$ whose $q$-expansion is obtained from some $g$ in the $\overline{\mathbb Q}$-base change of `qExpFunctionFieldC ℚ (Gamma0 M')` by multiplying all exponents by $q$, one has $x\in O$ if and only if $x\in O^{\mathrm{Ig}}([1:0])$.
--
--   This is the $q=2$ instance of the comparison, in the style of Deuring's constant reductions and Igusa's reduction of modular function fields, between an arbitrary valuation ring of the full-level field extending $A$ and dominating the level-$M'$ constant reduction, and the Gauss (Igusa) ring at the cusp $[1:0]$; the agreement is asserted only on the copy of the function field of $X_0(M')$ given by $q\mapsto q^q$ substitution, where good reduction at $q\nmid M'$ is available. It feeds the identification of $O$ with the Igusa ring in [`ModularCurve.FullLevel.exists_eq_igusaRing_of_forall_mem_integers_mem_of_eq_two`](thm.html#ModularCurve.FullLevel.exists_eq_igusaRing_of_forall_mem_integers_mem_of_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_mem_iff_mem_igusaGaussRing_of_coe_eq_qExpand_of_forall_mem_integers_mem_of_eq_two.lean

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

theorem ModularCurve.FullLevel.mem_iff_mem_igusaGaussRing_of_coe_eq_qExpand_of_forall_mem_integers_mem_of_eq_two
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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
