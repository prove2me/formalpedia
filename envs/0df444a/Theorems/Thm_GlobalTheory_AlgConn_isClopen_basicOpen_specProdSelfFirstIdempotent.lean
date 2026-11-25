-- Prove2me | Theorems.Thm_GlobalTheory_AlgConn_isClopen_basicOpen_specProdSelfFirstIdempotent
-- name    : GlobalTheory.AlgConn.isClopen_basicOpen_specProdSelfFirstIdempotent
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:55:41.210363+00:00
-- url     : https://prove2.me/theorems/0422cee1-2ece-45ff-b0bf-4eea4d4bee86
-- title:
--   Alg Conn: is Clopen basic Open spec Prod Self First Idempotent
-- statement:
--   The Alg Conn construction uses the is Clopen basic Open spec Prod Self First Idempotent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsClopenBasicOpenSpecProdSelfFirstIdempotent.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsClopenBasicOpenSpecProdSelfFirstIdempotent.lean#L21-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClopenBasicOpenSpecProdSelfFirstIdempotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.AlgConn

theorem GlobalTheory.AlgConn.isClopen_basicOpen_specProdSelfFirstIdempotent (O : Type) [CommRing O] :
    IsClopen (((Spec (.of (O × O))).basicOpen (fst1 O) : (Spec (.of (O × O))).Opens) :
      Set (Spec (.of (O × O)))) := by sorry
