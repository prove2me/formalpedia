-- Prove2me | Theorems.Thm_GlobalTheory_ClosedResidueExt_exists_unramified_ext
-- name    : GlobalTheory.ClosedResidueExt.exists_unramified_ext
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:13:16.684986+00:00
-- url     : https://prove2.me/theorems/ec58bde9-cd09-47c1-b2f3-cac3be575e7f
-- title:
--   Closed Residue Ext: exists unramified ext
-- statement:
--   The Closed Residue Ext construction uses the exists unramified ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsIntegralExtIsAlgClosedResidueField.lean#L248-L328
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsIntegralExtIsAlgClosedResidueField.lean#L248-L328

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

theorem GlobalTheory.ClosedResidueExt.exists_unramified_ext (W : Type) [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] {π : W} (hπ : Irreducible π) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (_ : Algebra W R), Function.Injective (algebraMap W R) ∧ Algebra.IsIntegral W R ∧
        Irreducible (algebraMap W R π) ∧ IsAlgClosed (ResidueField R) := by sorry
