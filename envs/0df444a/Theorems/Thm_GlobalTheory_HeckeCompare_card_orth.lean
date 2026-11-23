-- Prove2me | Theorems.Thm_GlobalTheory_HeckeCompare_card_orth
-- name    : GlobalTheory.HeckeCompare.card_orth
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:37:27.904325+00:00
-- url     : https://prove2.me/theorems/5f606d44-55f3-4f3b-86bc-2c1f9b391727
-- title:
--   Hecke Compare: card orth
-- statement:
--   The Hecke Compare construction uses the card orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NatCastMemConj.lean#L197-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NatCastMemConj.lean#L197-L230

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {k : Type} [Field k] {Q : Type} [CommGroup Q] {ρ : 𝓞 E → Q →* Q} {e : ℕ → Q → Q → kˣ → Prop}
  (I : TateIso D k Q (fun a x => ρ a x) e)
variable (hu : Uniq e)
include hu
include I

theorem GlobalTheory.HeckeCompare.card_orth [IsAlgClosed k] [CharZero k] {p : ℕ} (hp : 0 < p) (hf : Finite {x : Q // x ^ p = 1})
    (S : Subgroup Q) (hS : ∀ c ∈ S, c ^ p = 1) :
    Nat.card {x : Q // x ^ p = 1 ∧ ∀ c ∈ S, e p x c 1} * Nat.card S = Nat.card {x : Q // x ^ p = 1} := by sorry
