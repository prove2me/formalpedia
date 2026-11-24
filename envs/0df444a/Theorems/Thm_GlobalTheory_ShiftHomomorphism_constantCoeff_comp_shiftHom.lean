-- Prove2me | Theorems.Thm_GlobalTheory_ShiftHomomorphism_constantCoeff_comp_shiftHom
-- name    : GlobalTheory.ShiftHomomorphism.constantCoeff_comp_shiftHom
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:29:01.142681+00:00
-- url     : https://prove2.me/theorems/1d2963bc-cd0a-4a07-a403-e547d4ededa5
-- title:
--   Shift Homomorphism: constant Coeff comp shift Hom
-- statement:
--   The Shift Homomorphism construction uses the constant Coeff comp shift Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFormalBranchesOfSeparableReduction.lean#L15-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFormalBranchesOfSeparableReduction.lean#L15-L22

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

theorem GlobalTheory.ShiftHomomorphism.constantCoeff_comp_shiftHom (D : ℕ) (c : Fin D → ℂ) :
    (MvPowerSeries.constantCoeff (σ := Fin D) (R := ℂ)).comp (shiftHom D c).toRingHom
      = MvPolynomial.eval c := by sorry
