-- Prove2me | Theorems.Thm_GlobalTheory_SlocCong_flag_of_mem_N
-- name    : GlobalTheory.SlocCong.flag_of_mem_N
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:44:16.598611+00:00
-- url     : https://prove2.me/theorems/684d4c3f-a1ed-41b6-92fa-d06734d9ec5e
-- title:
--   Sloc Cong: flag of mem N
-- statement:
--   The Sloc Cong construction uses the flag of mem N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TermFamiliesCongrModUnitriangular.lean#L49-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TermFamiliesCongrModUnitriangular.lean#L49-L112

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermFamiliesCongrModUnitriangular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.MainNotions.S
open GlobalTheory GlobalTheory.SlocCong

theorem GlobalTheory.SlocCong.flag_of_mem_N {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V]
    [Module E V] {H : Loc.HermSp M V} {r : ℕ} (Fr : LocNG.FrameD H r) (g : V ≃ₗ[E] V) (hg : g ∈ Fr.N)
    (a : Fin (r + 1)) : g (Fr.f a) - Fr.f a ∈ Submodule.span E (Fr.f '' {c | c < a}) := by sorry
