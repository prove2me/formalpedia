-- Prove2me | Theorems.Thm_GlobalTheory_FibreMax_exists_isMaximal_height_ge
-- name    : GlobalTheory.FibreMax.exists_isMaximal_height_ge
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:24:18.999562+00:00
-- url     : https://prove2.me/theorems/5f114f9e-f507-4864-af53-8b47a13391b0
-- title:
--   Fibre Max: exists is Maximal height ge
-- statement:
--   The Fibre Max construction uses the exists is Maximal height ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMaximalHeightSuccDim.lean#L9-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMaximalHeightSuccDim.lean#L9-L56

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMaximalHeightSuccDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.FibreMax
attribute [local instance] Algebra.TensorProduct.rightAlgebra

theorem GlobalTheory.FibreMax.exists_isMaximal_height_ge (k : Type) [CommRing k] [IsDomain k] [Module.Finite ℤ k]
    [CharZero k] (A : Type) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [FaithfulSMul k A] (d : ℕ) (hd : ringKrullDim (FractionRing k ⊗[k] A) = d) :
    ∃ M : Ideal A, M.IsMaximal ∧ ((d + 1 : ℕ) : ℕ∞) ≤ M.height := by sorry
