-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_restrict_torsion
-- name    : GlobalTheory.AbLaw.restrict_torsion
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:21:08.261849+00:00
-- url     : https://prove2.me/theorems/ede35d72-a1ad-4318-9605-60e0dcc7af86
-- title:
--   Ab Law: restrict torsion
-- statement:
--   The Ab Law construction uses the restrict torsion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/AcyclicSliceSecCubeOfIsAffineOpen.lean#L43-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/AcyclicSliceSecCubeOfIsAffineOpen.lean#L43-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SecOnBasicOpenLocalization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AcyclicSliceSecCubeOfIsAffineOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.AbLaw
variable {Y : Scheme.{0}} (M : LB Y)
variable {M}

theorem GlobalTheory.AbLaw.restrict_torsion (hM : M.IsLB) {V W W' : Y.Opens} (hW : IsAffineOpen W)
    (hW' : IsAffineOpen W') (h : W ≤ V) (e : W' ≤ W) (a : Γ(Y, V))
    (ha : W ⊓ Y.basicOpen a ≤ W') :
    (∀ y : SecOn M W, SecOn.restrict M e y = 0 → ∃ n : ℕ, rs Y h (a ^ n) • y = 0) ∧
      ∀ z : SecOn M W', ∃ (n : ℕ) (y : SecOn M W),
        SecOn.restrict M e y = rs Y (e.trans h) (a ^ n) • z := by sorry
