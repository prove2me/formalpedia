-- Prove2me | Theorems.Thm_GlobalTheory_exists_finite_dvr_algHom_subset_range
-- name    : GlobalTheory.exists_finite_dvr_algHom_subset_range
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:31:30.890102+00:00
-- url     : https://prove2.me/theorems/1090a095-1faa-49f9-a39f-02013a18fa01
-- title:
--   Global Theory: exists finite dvr alg Hom subset range
-- statement:
--   The Global Theory construction uses the exists finite dvr alg Hom subset range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsFiniteDvrExtensionEmbeddingResidueField.lean#L73-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsFiniteDvrExtensionEmbeddingResidueField.lean#L73-L100

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsFiniteDvrExtensionEmbeddingResidueField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial IsLocalRing

theorem GlobalTheory.exists_finite_dvr_algHom_subset_range {B K : Type} [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [IsAdicComplete (maximalIdeal B) B] [Field K] [Algebra B K]
    [IsLocalHom (algebraMap B K)] [Module.Finite B K] (s : Finset K) :
    ∃ (B' : Type) (_ : CommRing B') (_ : IsDomain B') (_ : IsDiscreteValuationRing B')
      (_ : IsAdicComplete (maximalIdeal B') B') (_ : Algebra B B'), Module.Finite B B' ∧
      Function.Injective (algebraMap B B') ∧
      ∃ e : B' →ₐ[B] K, IsLocalHom (e : B' →+* K) ∧ (s : Set K) ⊆ Set.range e := by sorry
