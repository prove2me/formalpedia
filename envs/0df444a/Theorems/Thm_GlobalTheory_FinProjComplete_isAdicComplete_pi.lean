-- Prove2me | Theorems.Thm_GlobalTheory_FinProjComplete_isAdicComplete_pi
-- name    : GlobalTheory.FinProjComplete.isAdicComplete_pi
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:24:41.849661+00:00
-- url     : https://prove2.me/theorems/a8a30051-937f-421d-b765-b88ea0588f8a
-- title:
--   Fin Proj Complete: is Adic Complete pi
-- statement:
--   The Fin Proj Complete construction uses the is Adic Complete pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAdicCompleteSpanNatCastFiniteProjectiveAlgebra.lean#L18-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAdicCompleteSpanNatCastFiniteProjectiveAlgebra.lean#L18-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAdicCompleteSpanNatCastFiniteProjectiveAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FinProjComplete

theorem GlobalTheory.FinProjComplete.isAdicComplete_pi {R ι : Type*} [CommRing R] [Finite ι] (J : Ideal R)
    [IsAdicComplete J R] : IsAdicComplete J (ι → R) := by sorry
