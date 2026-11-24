-- Prove2me | Theorems.Thm_GlobalTheory_exists_basis_of_blockLowerTriangular_inv
-- name    : GlobalTheory.exists_basis_of_blockLowerTriangular_inv
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:30:33.028433+00:00
-- url     : https://prove2.me/theorems/3fa00d55-ed24-459f-8f6c-f24137c34cb5
-- title:
--   Global Theory: exists basis of block Lower Triangular inv
-- statement:
--   The Global Theory construction uses the exists basis of block Lower Triangular inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsBasisOfBlockLowerTriangularInv.lean#L7-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsBasisOfBlockLowerTriangularInv.lean#L7-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasisOfBlockLowerTriangularInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix

theorem GlobalTheory.exists_basis_of_blockLowerTriangular_inv (O M : Type) [CommRing O] [AddCommGroup M] [Module O M]
    (d k k' : ℕ) (lbs : Module.Basis (Fin k') O M)
    (P : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k') O) (P' : Matrix (Fin d ⊕ Fin k') (Fin d ⊕ Fin k) O)
    (h1 : P * P' = 1) (h2 : P' * P = 1) (hz : ∀ i j, P (Sum.inl i) (Sum.inr j) = 0) :
    ∃ lb : Module.Basis (Fin k) O M, ∀ j, lb j = ∑ j', P (Sum.inr j) (Sum.inr j') • lbs j' := by sorry
