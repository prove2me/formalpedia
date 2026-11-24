-- Prove2me | Theorems.Thm_GlobalTheory_exists_generators_dual_point_derivations
-- name    : GlobalTheory.exists_generators_dual_point_derivations
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:32:21.143955+00:00
-- url     : https://prove2.me/theorems/1b859788-22cc-46fe-b971-a3dadf069bbf
-- title:
--   Global Theory: exists generators dual point derivations
-- statement:
--   The Global Theory construction uses the exists generators dual point derivations property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGeneratorsDualPointDerivationsAugmented.lean#L6-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGeneratorsDualPointDerivationsAugmented.lean#L6-L120

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGeneratorsDualPointDerivationsAugmented
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory

theorem GlobalTheory.exists_generators_dual_point_derivations :
    ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] [Module.Finite k A] (ε : A →ₐ[k] k),
      IsNilpotent (RingHom.ker ε) → ∃ (d : ℕ) (x : Fin d → A) (l : Fin d → A →ₗ[k] k),
        (∀ i a b, l i (a * b) = ε a * l i b + ε b * l i a) ∧
        (∀ i j, l i (x j) = if i = j then 1 else 0) ∧ Algebra.adjoin k (Set.range x) = ⊤ := by sorry
