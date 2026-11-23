-- Prove2me | Theorems.Thm_GlobalTheory_EigenSplit_nonempty_basis
-- name    : GlobalTheory.EigenSplit.nonempty_basis
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:52:33.738848+00:00
-- url     : https://prove2.me/theorems/966b3b46-2133-434a-b100-e521777820e4
-- title:
--   Eigen Split: nonempty basis
-- statement:
--   The Eigen Split construction uses the nonempty basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L658-L661
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L658-L661

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct NumberField
open Polynomial
open GlobalTheory
open GlobalTheory.EigenSplit
variable {E : Type*} [Field E] [NumberField E] {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
  [DecidableEq ι]
omit [DecidableEq ι]

theorem GlobalTheory.EigenSplit.nonempty_basis (hc : Fintype.card ι = Module.finrank ℚ E) :
    Nonempty (Module.Basis ι ℤ (𝓞 E)) := by sorry
