-- Prove2me | Theorems.Thm_GlobalTheory_exists_isMaximal_tensorProduct_of_isLocalHom
-- name    : GlobalTheory.exists_isMaximal_tensorProduct_of_isLocalHom
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:33:17.180447+00:00
-- url     : https://prove2.me/theorems/136ae918-bcf3-439f-aa54-599047ee69d7
-- title:
--   Global Theory: exists is Maximal tensor Product of is Local Hom
-- statement:
--   The Global Theory construction uses the exists is Maximal tensor Product of is Local Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsIsMaximalTensorProductOfIsLocalHom.lean#L47-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsIsMaximalTensorProductOfIsLocalHom.lean#L47-L77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsIsMaximalTensorProductOfIsLocalHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory

theorem GlobalTheory.exists_isMaximal_tensorProduct_of_isLocalHom (O O' B : Type*) [CommRing O] [IsLocalRing O]
    [CommRing O'] [IsLocalRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')]
    [CommRing B] [Algebra O B] (I : Ideal B) (hI : I ≠ ⊤)
    (hm : Ideal.map (algebraMap O B) (IsLocalRing.maximalIdeal O) ≤ I) :
    ∃ M : Ideal (O' ⊗[O] B), M.IsMaximal ∧
      (∀ a ∈ IsLocalRing.maximalIdeal O', a ⊗ₜ[O] (1 : B) ∈ M) ∧
      ∀ b ∈ I, (1 : O') ⊗ₜ[O] b ∈ M := by sorry
