-- Prove2me | Theorems.Thm_GlobalTheory_EigenLine_finrank_ker_add_one
-- name    : GlobalTheory.EigenLine.finrank_ker_add_one
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:56:27.385793+00:00
-- url     : https://prove2.me/theorems/4414e095-6fa1-4bd2-ae61-296b908fd9ff
-- title:
--   Eigen Line: finrank ker add one
-- statement:
--   The Eigen Line construction uses the finrank ker add one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LineHyperplaneCut.lean#L58-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LineHyperplaneCut.lean#L58-L70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LineHyperplaneCut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory.EigenSplit
open GlobalTheory GlobalTheory.EigenLine
variable {K : Type} [Field K] {O : Type} [CommRing O] {L : Type} [AddCommGroup L] [Module K L]

theorem GlobalTheory.EigenLine.finrank_ker_add_one {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : V →ₗ[K] K) (hf : f ≠ 0) :
    Module.finrank K (LinearMap.ker f) + 1 = Module.finrank K V := by sorry
