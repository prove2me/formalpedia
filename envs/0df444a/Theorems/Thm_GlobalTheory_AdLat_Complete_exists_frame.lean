-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_Complete_exists_frame
-- name    : GlobalTheory.AdLat.Complete.exists_frame
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:54:40.034519+00:00
-- url     : https://prove2.me/theorems/aa63d9fd-36f3-4330-b10f-ec7d1046a6c2
-- title:
--   Complete: exists frame
-- statement:
--   The Complete construction uses the exists frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/AdelicCompletionLatticeSeparatedComplete.lean#L36-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/AdelicCompletionLatticeSeparatedComplete.lean#L36-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_SmulBasisMemHatIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IntegralFiniteAdeleCompleteSeparated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionLatticeSeparatedComplete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.Complete

theorem GlobalTheory.AdLat.Complete.exists_frame (R K V : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (M : Submodule R V) [Module.Finite R M] :
    ∃ (m : ℕ) (e : Fin m → V) (t : Fin m → (V →ₗ[K] K)), (∀ i, e i ∈ M) ∧
      (∀ i, ∀ v ∈ M, t i v ∈ (algebraMap R K).range) ∧ ∀ v ∈ M, ∑ i, t i v • e i = v := by sorry
