-- Prove2me | Theorems.Thm_GlobalTheory_SlocCong_stab_of_flag
-- name    : GlobalTheory.SlocCong.stab_of_flag
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:15:15.288564+00:00
-- url     : https://prove2.me/theorems/63c07fec-f6fb-4c1e-8826-e93633080fe9
-- title:
--   Sloc Cong: stab of flag
-- statement:
--   The Sloc Cong construction uses the stab of flag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TermFamiliesCongrModUnitriangular.lean#L7-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TermFamiliesCongrModUnitriangular.lean#L7-L20

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

theorem GlobalTheory.SlocCong.stab_of_flag {E : Type} [CommRing E] {V : Type} [AddCommGroup V] [Module E V] {n : ℕ}
    (f : Fin n → V) (g : V →ₗ[E] V)
    (hg : ∀ a, g (f a) - f a ∈ Submodule.span E (f '' {c | c < a})) (a : Fin n) :
    ∀ v ∈ Submodule.span E (f '' {c | c < a}), g v ∈ Submodule.span E (f '' {c | c < a}) := by sorry
