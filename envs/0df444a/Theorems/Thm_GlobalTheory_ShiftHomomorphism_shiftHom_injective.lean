-- Prove2me | Theorems.Thm_GlobalTheory_ShiftHomomorphism_shiftHom_injective
-- name    : GlobalTheory.ShiftHomomorphism.shiftHom_injective
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:28:27.896032+00:00
-- url     : https://prove2.me/theorems/56b9883b-9b91-46dd-8444-56fb68b71c90
-- title:
--   Shift Homomorphism: shift Hom injective
-- statement:
--   The Shift Homomorphism construction uses the shift Hom injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFormalBranchesOfSeparableReduction.lean#L24-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFormalBranchesOfSeparableReduction.lean#L24-L38

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

theorem GlobalTheory.ShiftHomomorphism.shiftHom_injective (D : ℕ) (c : Fin D → ℂ) : Function.Injective (shiftHom D c) := by sorry
