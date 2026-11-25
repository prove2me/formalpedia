-- Prove2me | Theorems.Thm_GlobalTheory_SepRing_exists_complete_local_geomDomain
-- name    : GlobalTheory.SepRing.exists_complete_local_geomDomain
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:06:23.298934+00:00
-- url     : https://prove2.me/theorems/923a8a42-ca66-4d07-825f-1644dbb396ce
-- title:
--   Sep Ring: exists complete local geom Domain
-- statement:
--   The Sep Ring construction uses the exists complete local geom Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCompleteLocalGeomDomain.lean#L66-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCompleteLocalGeomDomain.lean#L66-L99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsRingEquivAdicCompletionLocalizationProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsRegularLocalRingAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsNoetherianRingAdicCompletionOfNoetherian
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdempotentTensorEqZeroOrOneOfIsPurelyInseparableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRegularLocalRingAtPrimeLocalizationTensorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompleteLocalGeomDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open scoped TensorProduct
open GlobalTheory GlobalTheory.SepRing
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

theorem GlobalTheory.SepRing.exists_complete_local_geomDomain : ∀ (k k' : Type) [Field k] [CommRing k'] [IsDomain k']
    [Algebra k k'], Module.Finite k k' → ∃ (C : Type) (_ : CommRing C) (_ : IsLocalRing C)
    (_ : IsNoetherianRing C) (_ : Algebra k C), IsAdicComplete (maximalIdeal C) C ∧
    Nonempty (k' →ₐ[k] ResidueField C) ∧ ∀ (K : Type) [Field K] [Algebra k K],
    FiniteDimensional k K → IsPurelyInseparable k K → IsDomain (K ⊗[k] C) := by sorry
