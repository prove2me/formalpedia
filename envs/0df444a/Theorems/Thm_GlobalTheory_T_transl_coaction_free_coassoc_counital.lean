-- Prove2me | Theorems.Thm_GlobalTheory_T_transl_coaction_free_coassoc_counital
-- name    : GlobalTheory.T.transl_coaction_free_coassoc_counital
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:13:10.11996+00:00
-- url     : https://prove2.me/theorems/d2116a38-13b1-4b4f-aa65-ee3250543def
-- title:
--   T: transl coaction free coassoc counital
-- statement:
--   The T construction uses the transl coaction free coassoc counital property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TranslCoactionFreeCoassocCounitalStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TranslCoactionFreeCoassocCounitalStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TranslCoactionFreeCoassocCounital
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TranslCoactionFreeCoassocCounitalStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.transl_coaction_free_coassoc_counital : ∀ {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (n : ℕ), (∀ a, TensorProduct.assoc R (G.A (n + 1)) (G.A 1) (G.A 1) ((G.transl n).toLinearMap.rTensor (G.A 1) (G.transl n a)) = (Coalgebra.comul (R := R) (A := G.A 1)).lTensor (G.A (n + 1)) (G.transl n a)) ∧ (∀ a, TensorProduct.rid R (G.A (n + 1)) ((Coalgebra.counit (R := R) (A := G.A 1)).lTensor (G.A (n + 1)) (G.transl n a)) = a) ∧ Function.Surjective (Algebra.TensorProduct.productMap (Algebra.TensorProduct.includeLeft : G.A (n + 1) →ₐ[R] G.A (n + 1) ⊗[R] G.A 1) (G.transl n)) := by sorry
