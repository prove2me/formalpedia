-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_generators_dual_point_derivations_augmented
-- name    : GlobalTheory.T.exists_generators_dual_point_derivations_augmented
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:36:06.714952+00:00
-- url     : https://prove2.me/theorems/917f6869-a59f-4d87-af80-a892366e4dfc
-- title:
--   T: exists generators dual point derivations augmented
-- statement:
--   The T construction uses the exists generators dual point derivations augmented property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGeneratorsDualPointDerivationsAugmentedStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGeneratorsDualPointDerivationsAugmentedStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGeneratorsDualPointDerivationsAugmented
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGeneratorsDualPointDerivationsAugmentedStatement
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

theorem GlobalTheory.T.exists_generators_dual_point_derivations_augmented : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] [Module.Finite k A] (ε : A →ₐ[k] k), IsNilpotent (RingHom.ker ε) → ∃ (d : ℕ) (x : Fin d → A) (l : Fin d → A →ₗ[k] k), (∀ i a b, l i (a * b) = ε a * l i b + ε b * l i a) ∧ (∀ i j, l i (x j) = if i = j then 1 else 0) ∧ Algebra.adjoin k (Set.range x) = ⊤ := by sorry
