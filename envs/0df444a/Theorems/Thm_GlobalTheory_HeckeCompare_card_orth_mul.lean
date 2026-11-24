-- Prove2me | Theorems.Thm_GlobalTheory_HeckeCompare_card_orth_mul
-- name    : GlobalTheory.HeckeCompare.card_orth_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:01:52.477519+00:00
-- url     : https://prove2.me/theorems/b5606863-a893-46d2-9e1f-9d7a94f2a8ea
-- title:
--   Hecke Compare: card orth mul
-- statement:
--   The Hecke Compare construction uses the card orth mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NatCastMemConj.lean#L12-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NatCastMemConj.lean#L12-L27

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

theorem GlobalTheory.HeckeCompare.card_orth_mul {G k : Type} [CommGroup G] [Finite G] [Field k] [IsAlgClosed k] [CharZero k]
    (B : G →* G →* kˣ) (hB : Function.Injective B) (S : Subgroup G) :
    Nat.card {x : G // ∀ c ∈ S, B x c = 1} * Nat.card S = Nat.card G := by sorry
