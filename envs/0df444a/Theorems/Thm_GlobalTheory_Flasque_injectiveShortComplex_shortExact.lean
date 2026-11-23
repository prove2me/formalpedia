-- Prove2me | Theorems.Thm_GlobalTheory_Flasque_injectiveShortComplex_shortExact
-- name    : GlobalTheory.Flasque.injectiveShortComplex_shortExact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:01:08.44736+00:00
-- url     : https://prove2.me/theorems/5cfbce9a-3500-4781-912b-0c50298ab663
-- title:
--   Flasque: injective Short Complex short Exact
-- statement:
--   The Flasque construction uses the injective Short Complex short Exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CohomologyPresheafFunctorMapAppApply.lean#L226-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CohomologyPresheafFunctorMapAppApply.lean#L226-L228

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Abelian Opposite Limits TopologicalSpace
universe w v u
open GlobalTheory
open GlobalTheory.Flasque
variable {A : Type u} [Category.{v} A] [Abelian A]
open CategoryTheory Abelian Opposite Limits TopologicalSpace
variable {A : Type u} [Category.{v} A] [Abelian A]

theorem GlobalTheory.Flasque.injectiveShortComplex_shortExact [EnoughInjectives A] (F : A) :
    (_root_.GlobalTheory.Flasque.injectiveShortComplex F).ShortExact := by sorry
