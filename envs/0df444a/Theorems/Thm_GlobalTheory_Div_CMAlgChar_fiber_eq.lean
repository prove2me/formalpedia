-- Prove2me | Theorems.Thm_GlobalTheory_Div_CMAlgChar_fiber_eq
-- name    : GlobalTheory.Div.CMAlgChar.fiber_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:50:37.298135+00:00
-- url     : https://prove2.me/theorems/6cad6d08-8000-4185-bef3-0dc58c8b14fd
-- title:
--   CMAlg Char: fiber eq
-- statement:
--   The CMAlg Char construction uses the fiber eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmAlgCharEqArgMulAbs.lean#L27-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmAlgCharEqArgMulAbs.lean#L27-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmAlgCharEqArgMulAbs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.Div GlobalTheory.Div.CMAlgChar

theorem GlobalTheory.Div.CMAlgChar.fiber_eq {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] [DecidableEq (E →+* ℂ)]
    [DecidableEq (InfinitePlace E)]
    (w : InfinitePlace E) :
    (Finset.univ.filter fun φ : E →+* ℂ => InfinitePlace.mk φ = w) =
      {w.embedding, ComplexEmbedding.conjugate w.embedding} := by sorry
