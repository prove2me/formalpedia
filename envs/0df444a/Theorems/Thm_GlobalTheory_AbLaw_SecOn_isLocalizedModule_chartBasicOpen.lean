-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_SecOn_isLocalizedModule_chartBasicOpen
-- name    : GlobalTheory.AbLaw.SecOn.isLocalizedModule_chartBasicOpen
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:29:39.896644+00:00
-- url     : https://prove2.me/theorems/dde0861c-9a24-4bfc-90dd-500f012999c1
-- title:
--   Sec On: is Localized Module chart Basic Open
-- statement:
--   The Sec On construction uses the is Localized Module chart Basic Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SecOnFinitePresentationProjective.lean#L24-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SecOnFinitePresentationProjective.lean#L24-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SecOnBasicOpenLocalization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SecOnFinitePresentationProjective
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
variable {Y : Scheme.{0}} {M : LB Y} {V : Y.Opens}

theorem GlobalTheory.AbLaw.SecOn.isLocalizedModule_chartBasicOpen (hM : M.IsLB) (hV : IsAffineOpen V) (i : M.ι)
    (a : Γ(Y, V)) (h : Y.basicOpen a ≤ M.U i) :
    IsLocalizedModule (Submonoid.powers a) (SecOn.chartBasicOpen hM i a h) := by sorry
