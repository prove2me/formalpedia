-- Prove2me | Theorems.Thm_GlobalTheory_DetCompare_hasEigenDim_iff
-- name    : GlobalTheory.DetCompare.hasEigenDim_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:05:16.51741+00:00
-- url     : https://prove2.me/theorems/ade6cc14-273e-40d7-a083-1ae68d3ee29e
-- title:
--   Det Compare: has Eigen Dim iff
-- statement:
--   The Det Compare construction uses the has Eigen Dim iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DetCondIffHasMultiplicities.lean#L118-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DetCondIffHasMultiplicities.lean#L118-L131

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_LieCharpolyRootPairs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsTangentModuleUniversalGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DetCondIffHasMultiplicities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DetCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LieCharpolyRootPairs GlobalTheory.TanMod GlobalTheory.EigenSplit
variable {S : Scheme.{0}} {k : Type} [Field k]
variable {G : Over S} [GrpObj G] {O : Type} [CommRing O]
variable [IsCommMonObj G]

theorem GlobalTheory.DetCompare.hasEigenDim_iff (act : OAct O G) (t : Sp k ⟶ S) (τ : O →+* k) (n : ℕ) :
    HasEigenDim act t τ n ↔ Module.Finite k (eigenSub (TanSp.act t act) τ) ∧
      Module.finrank k (eigenSub (TanSp.act t act) τ) = n := by sorry
