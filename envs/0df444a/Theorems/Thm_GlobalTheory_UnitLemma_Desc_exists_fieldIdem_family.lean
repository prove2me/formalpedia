-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Desc_exists_fieldIdem_family
-- name    : GlobalTheory.UnitLemma.Desc.exists_fieldIdem_family
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:27:54.465929+00:00
-- url     : https://prove2.me/theorems/0017f20b-2237-4106-a4c0-f9fc9ab82b49
-- title:
--   Desc: exists field Idem family
-- statement:
--   The Desc construction uses the exists field Idem family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/InvolutionIdempotentDecompositionOfSeparableChar.lean#L54-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/InvolutionIdempotentDecompositionOfSeparableChar.lean#L54-L91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsReducedOfSeparableMarkedCharpoly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvolutionIdempotentDecompositionOfSeparableChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc
open Classical
variable {R : Type} [CommRing R]

theorem GlobalTheory.UnitLemma.Desc.exists_fieldIdem_family [IsReduced R] [IsArtinianRing R] :
    ∃ (M : Type) (_ : Fintype M) (f : M → R), CompleteOrthogonalIdempotents f ∧ ∀ m, FieldIdem (f m) := by sorry
