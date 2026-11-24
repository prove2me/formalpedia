-- Prove2me | Theorems.Thm_GlobalTheory_ClosedResidueExt_exists_integral_ext_isAlgClosed_residueField
-- name    : GlobalTheory.ClosedResidueExt.exists_integral_ext_isAlgClosed_residueField
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:12:53.286539+00:00
-- url     : https://prove2.me/theorems/f218e96c-717f-49e1-9190-7003a4caf31b
-- title:
--   Closed Residue Ext: exists integral ext is Alg Closed residue Field
-- statement:
--   The Closed Residue Ext construction uses the exists integral ext is Alg Closed residue Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsIntegralExtIsAlgClosedResidueField.lean#L333-L341
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsIntegralExtIsAlgClosedResidueField.lean#L333-L341

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIntegralExtIsAlgClosedResidueField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ClosedResidueExt
open Polynomial IsLocalRing
variable {W Ω : Type} [CommRing W] [Field Ω] [Algebra W Ω]
open Polynomial IsLocalRing
variable {W Ω : Type} [CommRing W] [Field Ω] [Algebra W Ω]

theorem GlobalTheory.ClosedResidueExt.exists_integral_ext_isAlgClosed_residueField : ∀ (W : Type) [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W] [CharZero W],
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (_ : Algebra W R), Function.Injective (algebraMap W R) ∧ Algebra.IsIntegral W R ∧
        IsAlgClosed (IsLocalRing.ResidueField R) := by sorry
