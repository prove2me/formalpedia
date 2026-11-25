-- Prove2me | Theorems.Thm_GlobalTheory_BiextSym_exists_norm
-- name    : GlobalTheory.BiextSym.exists_norm
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T16:50:33.570788+00:00
-- url     : https://prove2.me/theorems/ddf1daf4-650c-5214-aef8-8a619fe8d3a0
-- title:
--   Biext Sym: exists norm
-- statement:
--   The Biext Sym construction uses the exists norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/BiextensionSecondLawProduct.lean#L78-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/BiextensionSecondLawProduct.lean#L78-L92

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_BiextensionSecondLawProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.BiextSym
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

theorem GlobalTheory.BiextSym.exists_norm {P : LB (A ⊗ A).left} (hP : P.IsLB) (h : LBIso P (P.pull (lift (snd A A) (fst A A)).left)) :
    ∃ s : LB.Gen (LB.LinComb P (K := Fin 2) ![(lift (snd A A) (fst A A)).left, 𝟙 (A ⊗ A).left] ![1, -1]), s.IsGen ∧
      ∀ (T : Over S) (z : T.left) (J), Good P z J → val s (lift (1 : T ⟶ A) (1 : T ⟶ A)).left z J = 1 := by sorry
