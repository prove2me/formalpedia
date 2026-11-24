-- Prove2me | Theorems.Thm_GlobalTheory_Ex_QStr_split_ext
-- name    : GlobalTheory.Ex.QStr.split_ext
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:07:45.668898+00:00
-- url     : https://prove2.me/theorems/c3f9814f-bdea-4c69-bccc-fbd4dce123b6
-- title:
--   QStr: split ext
-- statement:
--   The QStr construction uses the split ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/DegenerationDataTorsionStructureAlgClosed.lean#L84-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/DegenerationDataTorsionStructureAlgClosed.lean#L84-L97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.QStr

theorem GlobalTheory.Ex.QStr.split_ext {M : Type} [CommGroup M] (k a d : ℕ) [NeZero k] (hM : ∀ x : M, x ^ k = 1)
    (i : Multiplicative (Fin d → ZMod k) →* M) (π : M →* Multiplicative (Fin a → ZMod k))
    (hi : Function.Injective i) (hπ : Function.Surjective π) (hex : ∀ x, π x = 1 ↔ ∃ y, i y = x) :
    Nonempty (M ≃* Multiplicative (Fin (a + d) → ZMod k)) := by sorry
