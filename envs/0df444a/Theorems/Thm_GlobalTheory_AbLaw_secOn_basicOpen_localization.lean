-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_secOn_basicOpen_localization
-- name    : GlobalTheory.AbLaw.secOn_basicOpen_localization
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T15:09:18.273813+00:00
-- url     : https://prove2.me/theorems/29de1443-765b-5638-9263-2d9c2fcb8b7e
-- title:
--   Ab Law: sec On basic Open localization
-- statement:
--   The Ab Law construction uses the sec On basic Open localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SecOnBasicOpenLocalization.lean#L14-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SecOnBasicOpenLocalization.lean#L14-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SecOnBasicOpenLocalization
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
open GlobalTheory GlobalTheory.AbLaw

theorem GlobalTheory.AbLaw.secOn_basicOpen_localization :
    ∀ (Y : Scheme.{0}) (M : LB Y) (V W : Y.Opens) (a : Γ(Y, V)) (h : W ≤ V), M.IsLB → IsCompact (V : Set Y) → IsQuasiSeparated (V : Set Y) → W = Y.basicOpen a → (∀ x : SecOn M V, SecOn.restrict M h x = 0 → ∃ k : ℕ, a ^ k • x = 0) ∧ ∀ y : SecOn M W, ∃ (k : ℕ) (x : SecOn M V), SecOn.restrict M h x = rs Y h a ^ k • y := by sorry
