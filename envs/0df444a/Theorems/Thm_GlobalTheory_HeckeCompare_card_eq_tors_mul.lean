-- Prove2me | Theorems.Thm_GlobalTheory_HeckeCompare_card_eq_tors_mul
-- name    : GlobalTheory.HeckeCompare.card_eq_tors_mul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:01:39.424966+00:00
-- url     : https://prove2.me/theorems/af20de63-7019-4d48-84a3-300f7cd237a7
-- title:
--   Hecke Compare: card eq tors mul
-- statement:
--   The Hecke Compare construction uses the card eq tors mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NatCastMemConj.lean#L29-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NatCastMemConj.lean#L29-L34

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUnimodDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NatCastMemConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HeckeCompare

theorem GlobalTheory.HeckeCompare.card_eq_tors_mul {Q : Type} [CommGroup Q] (C : Subgroup Q) (p : ℕ) :
    Nat.card C = Nat.card {x : Q // x ∈ C ∧ x ^ p = 1} * Nat.card (C.map (powMonoidHom p)) := by sorry
