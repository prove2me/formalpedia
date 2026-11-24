-- Prove2me | Theorems.Thm_GlobalTheory_HeckeCompare_natCast_mem_conj
-- name    : GlobalTheory.HeckeCompare.natCast_mem_conj
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T14:03:14.380031+00:00
-- url     : https://prove2.me/theorems/ce92f057-6d5c-42ec-a602-c43548e29db5
-- title:
--   Hecke Compare: nat Cast mem conj
-- statement:
--   The Hecke Compare construction uses the nat Cast mem conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NatCastMemConj.lean#L244-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NatCastMemConj.lean#L244-L247

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

theorem GlobalTheory.HeckeCompare.natCast_mem_conj {P : Ideal (𝓞 E)} {p : ℕ} (h : (p : 𝓞 E) ∈ P) :
    (p : 𝓞 E) ∈ P.map (H.bar : 𝓞 E →+* 𝓞 E) := by sorry
