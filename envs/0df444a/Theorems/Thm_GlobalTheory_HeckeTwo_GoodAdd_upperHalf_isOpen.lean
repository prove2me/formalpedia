-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_GoodAdd_upperHalf_isOpen
-- name    : GlobalTheory.HeckeTwo.GoodAdd.upperHalf_isOpen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:52:26.755798+00:00
-- url     : https://prove2.me/theorems/1cf12e1d-8d33-448d-b709-e53214e07dfd
-- title:
--   Good Add: upper Half is Open
-- statement:
--   The Good Add construction uses the upper Half is Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSmoothHolomorphicInSigmaFamilyAdd.lean#L57-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSmoothHolomorphicInSigmaFamilyAdd.lean#L57-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.GoodAdd
variable {Φ : Type} [Fintype Φ]

theorem GlobalTheory.HeckeTwo.GoodAdd.upperHalf_isOpen (F : Type) [Field F] [NumberField F] : IsOpen (upperHalf F) := by sorry
