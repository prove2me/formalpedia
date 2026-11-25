-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_separable_point_of_geometrically_domain
-- name    : GlobalTheory.T.exists_separable_point_of_geometrically_domain
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:31:43.673928+00:00
-- url     : https://prove2.me/theorems/be205a47-1ded-4324-ad1d-68390ea8c188
-- title:
--   T: exists separable point of geometrically domain
-- statement:
--   The T construction uses the exists separable point of geometrically domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSeparablePointOfGeometricallyDomainStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSeparablePointOfGeometricallyDomainStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSeparablePointOfGeometricallyDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSeparablePointOfGeometricallyDomainStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_separable_point_of_geometrically_domain : ∀ (k B : Type) [Field k] [CommRing B] [Algebra k B], Algebra.FiniteType k B → (∀ (K : Type) [Field K] [Algebra k K], FiniteDimensional k K → IsPurelyInseparable k K → IsDomain (K ⊗[k] B)) → ∃ (k' : Type) (_ : Field k') (_ : Algebra k k'), FiniteDimensional k k' ∧ Algebra.IsSeparable k k' ∧ Nonempty (B →ₐ[k] k') := by sorry
