-- Prove2me | Theorems.Thm_IterOmega_IterStar
-- name    : IterOmega_IterStar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:25:02.965335+00:00
-- url     : https://prove2.me/theorems/c218e37e-8a02-468b-98ef-df86656b48cf
-- title:
--   Iter Omega Iter Star: Iter Omega Iter Star
-- statement:
--   The Iter Omega Iter Star construction uses the Iter Omega Iter Star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/Basic.lean#L275-L335
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/Basic.lean#L275-L335

import Definitions.Def_AutomataTheory_Sequences_Segments
import Definitions.Def_AutomataTheory_Languages_Basic
set_option autoImplicit true
open Function Finset Set Filter Stream'
open scoped Computability
variable {A : Type}

theorem IterOmega_IterStar {L : Set (List A)} :
    (L∗)^ω = L^ω := by sorry
