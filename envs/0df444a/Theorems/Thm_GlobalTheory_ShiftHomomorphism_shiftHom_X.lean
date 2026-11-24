-- Prove2me | Theorems.Thm_GlobalTheory_ShiftHomomorphism_shiftHom_X
-- name    : GlobalTheory.ShiftHomomorphism.shiftHom_X
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:29:24.331171+00:00
-- url     : https://prove2.me/theorems/59a69ad2-75cf-4b97-95dc-868b7951417f
-- title:
--   Shift Homomorphism: shift Hom X
-- statement:
--   The Shift Homomorphism construction uses the shift Hom X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFormalBranchesOfSeparableReduction.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFormalBranchesOfSeparableReduction.lean#L11-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLiftsOfSeparableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFormalBranchesOfSeparableReduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.ShiftHomomorphism

theorem GlobalTheory.ShiftHomomorphism.shiftHom_X (D : ℕ) (c : Fin D → ℂ) (i : Fin D) :
    shiftHom D c (MvPolynomial.X i) = MvPowerSeries.X i + MvPowerSeries.C (c i) := by sorry
