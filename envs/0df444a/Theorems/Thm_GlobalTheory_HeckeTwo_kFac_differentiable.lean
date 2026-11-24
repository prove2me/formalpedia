-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_kFac_differentiable
-- name    : GlobalTheory.HeckeTwo.kFac_differentiable
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:27:38.346651+00:00
-- url     : https://prove2.me/theorems/c8deb267-87fd-4b7b-b302-a03d390c390b
-- title:
--   Hecke Two: k Fac differentiable
-- statement:
--   The Hecke Two construction uses the k Fac differentiable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KFacDifferentiable.lean#L59-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KFacDifferentiable.lean#L59-L67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Complex MeasureTheory
open scoped nonZeroDivisors ContDiff
open GlobalTheory GlobalTheory.HeckeTwo
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.HeckeTwo.kFac_differentiable : Differentiable ℂ (kFac F) := by sorry
