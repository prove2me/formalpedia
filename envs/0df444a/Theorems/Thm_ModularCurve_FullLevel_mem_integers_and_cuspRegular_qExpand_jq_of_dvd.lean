-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_mem_integers_and_cuspRegular_qExpand_jq_of_dvd
-- name    : ModularCurve.FullLevel.mem_integers_and_cuspRegular_qExpand_jq_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/22faca84-ab74-504c-8fd8-72bda3fe87fe
-- title:
--   Integrality and cusp-regularity of j(qᵈ) for d ∣ M'
-- statement:
--   Fix $M' \ge 1$ and a valuation subring $A$ of $\overline{\mathbb Q}$, and let $F =$ `modularFunctionFieldBar M'` be the subfield of $\overline{\mathbb Q}((q))$ generated over $\overline{\mathbb Q}$ by the coefficientwise images of the level-$M'$ modular function field `modularFunctionFieldFull M'` $\subset \mathbb Q((q))$. Let $R_0$ be a `ConstantReduction` of $F$ along $A$ with values in `modularFunctionFieldC (ResidueField A) M'`, the subfield of $k((q))$, $k = \mathrm{ResidueField}\,A$, generated over $k$ by `jqModC k` and its $q \mapsto q^{M'}$ substitution `jqNModC k M'`; thus $R_0$ consists of a valuation subring $R_0.\mathrm{integers}$ of $F$, a surjective residue map onto that field with kernel the maximal ideal, a map on places preserving degrees and orders, and the compatibilities with $A$ recorded in the structure. Assume $R_0$ is pinned by $h_{R_0}$: every Laurent series $y$ over $A$ whose coefficientwise image in $\overline{\mathbb Q}((q))$ lies in $F$ is an element of $R_0.\mathrm{integers}$ whose residue is, as a Laurent series over $k$, the coefficientwise reduction of $y$. Let $d \ge 1$ divide $M'$. Then the element $j(q^d) =$ `coeffEmb` $(q\mapsto q^d$ substitution of $j)$ of $F$ lies in $R_0.\mathrm{integers}$, and for every place $P$ of $F$ over $\overline{\mathbb Q}$ with $\mathrm{ord}_P\, j(q) \ge 0$ one has $\mathrm{ord}_P\, j(q^d) \ge 0$.
--
--   This is the standard admissibility statement for the functions $j(q^d)$, $d \mid M'$, which generate the full level-$M'$ modular function field: $j(q^d)$ is a root of the modular polynomial $\Phi_d(X, j(q))$, monic in $X$, hence integral over $\mathbb Q[j(q)]$ and regular wherever $j(q)$ is, while its integral $q$-expansion makes it $R_0$-integral with the expected reduction. It feeds the construction of specializations of the level-$M'$ modular function field at Tate points and the associated moduli places and Frobenius comparisons.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_mem_integers_and_cuspRegular_qExpand_jq_of_dvd.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_EllipticCurve_WeilPairingFun
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_ModuliPlace
import Definitions.Def_ModularCurve_ModuliPointMap
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups Classical

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.mem_integers_and_cuspRegular_qExpand_jq_of_dvd
    (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (d : ℕ) [NeZero d] (hd : d ∣ M') :
    (⟨coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ d ModularCurve.jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.jqd_mem_full M' hd)⟩ :
        ↥(modularFunctionFieldBar M')) ∈ R₀.integers ∧
    (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
      0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
      0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ d ModularCurve.jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.jqd_mem_full M' hd)⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M'))) := by sorry
