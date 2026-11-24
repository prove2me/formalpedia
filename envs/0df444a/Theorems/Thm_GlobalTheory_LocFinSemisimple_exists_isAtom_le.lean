-- Prove2me | Theorems.Thm_GlobalTheory_LocFinSemisimple_exists_isAtom_le
-- name    : GlobalTheory.LocFinSemisimple.exists_isAtom_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:12:06.222941+00:00
-- url     : https://prove2.me/theorems/eb7ed32f-2ab9-45fd-9014-7d74967136d0
-- title:
--   Loc Fin Semisimple: exists is Atom le
-- statement:
--   The Loc Fin Semisimple construction uses the exists is Atom le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/IsSemisimpleOfLocallyFiniteCompactGroup.lean#L8-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/IsSemisimpleOfLocallyFiniteCompactGroup.lean#L8-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegralConjInnerMulInnerOfIsEmptyEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_IsSemisimpleOfLocallyFiniteCompactGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LocFinSemisimple
variable {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ K V}

theorem GlobalTheory.LocFinSemisimple.exists_isAtom_le : ∀ (n : ℕ) (Y : Subrepresentation ρ),
    FiniteDimensional ℂ Y.toSubmodule → Module.finrank ℂ Y.toSubmodule = n → Y ≠ ⊥ →
      ∃ T : Subrepresentation ρ, IsAtom T ∧ T ≤ Y := by sorry
