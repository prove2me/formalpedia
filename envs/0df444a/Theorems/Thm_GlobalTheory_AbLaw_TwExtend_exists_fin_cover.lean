-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_TwExtend_exists_fin_cover
-- name    : GlobalTheory.AbLaw.TwExtend.exists_fin_cover
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:26:49.765681+00:00
-- url     : https://prove2.me/theorems/8177de1e-c5fe-5728-a523-e7a85c18870e
-- title:
--   Tw Extend: exists fin cover
-- statement:
--   The Tw Extend construction uses the exists fin cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsTwExtendPowMul.lean#L39-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsTwExtendPowMul.lean#L39-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsTwExtendPowMul
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
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.TwExtend
variable {Y : Scheme.{0}}

theorem GlobalTheory.AbLaw.TwExtend.exists_fin_cover [CompactSpace Y] {M H : LB Y} (hM : M.IsLB) (hH : H.IsLB) :
    ∃ (κ : Type) (_ : Fintype κ) (W : κ → Y.Opens) (p : κ → M.ι) (l : κ → H.ι),
      (∀ a, IsAffineOpen (W a)) ∧ (∀ a, W a ≤ M.U (p a) ⊓ H.U (l a)) ∧ ⊤ ≤ ⨆ a, W a := by sorry
