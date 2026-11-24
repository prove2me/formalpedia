-- Prove2me | Theorems.Thm_GlobalTheory_Mem_Chr_Model_infIdele_fst_ne
-- name    : GlobalTheory.Mem.Chr.Model.infIdele_fst_ne
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:23:05.892179+00:00
-- url     : https://prove2.me/theorems/f9040d69-2842-4d01-83ea-c08ac8b65cb4
-- title:
--   Model: inf Idele fst ne
-- statement:
--   The Model construction uses the inf Idele fst ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/DiagUnitsEqLocalIdele.lean#L32-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/DiagUnitsEqLocalIdele.lean#L32-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ValuedAlgebraMapEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_DiagUnitsEqLocalIdele
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Chr.Model
variable (L : Type) [Field L] [NumberField L]

theorem GlobalTheory.Mem.Chr.Model.infIdele_fst_ne (w u : InfinitePlace L) (h : u ≠ w) (x : (w.Completion)ˣ) :
    ((infIdele L w x : Ideles L) : AdeleRing (𝓞 L) L).1 u = 1 := by sorry
