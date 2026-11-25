-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_hom_specProdSelf_preimage_eq_clopen
-- name    : GlobalTheory.T.exists_hom_specProdSelf_preimage_eq_clopen
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:29:11.659553+00:00
-- url     : https://prove2.me/theorems/f0549f76-ce46-5c29-ad5e-feafb1467cbc
-- title:
--   T: exists hom spec Prod Self preimage eq clopen
-- statement:
--   The T construction uses the exists hom spec Prod Self preimage eq clopen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsHomSpecProdSelfPreimageEqClopenStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsHomSpecProdSelfPreimageEqClopenStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHomSpecProdSelfPreimageEqClopen
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClopenBasicOpenSpecProdSelfFirstIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdempotentOfClopen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdempotentEqOfBasicOpenEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHomSpecProdSelfPreimageEqClopenStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.AlgConn
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_hom_specProdSelf_preimage_eq_clopen : ∀ (O : Type) [CommRing O] (T : Scheme.{0}) (p : T ⟶ Spec (.of O)) (U : Set T), IsClopen U → ∃ h : T ⟶ Spec (.of (O × O)), h ≫ twoπ O = p ∧ ((h ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) : T.Opens) : Set T) = U := by sorry
