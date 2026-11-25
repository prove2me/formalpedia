-- Prove2me | Theorems.Thm_GlobalTheory_T_hom_ext_specProdSelf_of_basicOpen_preimage_eq
-- name    : GlobalTheory.T.hom_ext_specProdSelf_of_basicOpen_preimage_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:33:07.384803+00:00
-- url     : https://prove2.me/theorems/7e2e04bb-f6a8-4746-9e13-a8ecca93ca23
-- title:
--   T: hom ext spec Prod Self of basic Open preimage eq
-- statement:
--   The T construction uses the hom ext spec Prod Self of basic Open preimage eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HomExtSpecProdSelfOfBasicOpenPreimageEqStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HomExtSpecProdSelfOfBasicOpenPreimageEqStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomExtSpecProdSelfOfBasicOpenPreimageEq
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClopenBasicOpenSpecProdSelfFirstIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdempotentOfClopen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdempotentEqOfBasicOpenEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomExtSpecProdSelfOfBasicOpenPreimageEqStatement
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

theorem GlobalTheory.T.hom_ext_specProdSelf_of_basicOpen_preimage_eq : ∀ (O : Type) [CommRing O] (T : Scheme.{0}) (h h' : T ⟶ Spec (.of (O × O))), h ≫ twoπ O = h' ≫ twoπ O → h ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) = h' ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) → h = h' := by sorry
