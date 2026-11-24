-- Prove2me | Theorems.Thm_GlobalTheory_HeckeCompare_triv_of_primary
-- name    : GlobalTheory.HeckeCompare.triv_of_primary
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:02:57.4964+00:00
-- url     : https://prove2.me/theorems/d02875b5-aa92-4401-a9e1-2ee7582ad7d7
-- title:
--   Hecke Compare: triv of primary
-- statement:
--   The Hecke Compare construction uses the triv of primary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NatCastMemConj.lean#L258-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NatCastMemConj.lean#L258-L268

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
variable (I : TateIso D k Q (fun a x => ρ a x) e) (hu : Uniq e) (hρ : IsAct ρ) {P : Ideal (𝓞 E)} [hP : P.IsMaximal]
  (hco : P ⊔ P.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤) {p : ℕ} (hp : 0 < p) (hpP : (p : 𝓞 E) ∈ P)
include I hu hρ hco
omit hP

theorem GlobalTheory.HeckeCompare.triv_of_primary {n : ℕ} (hn : 0 < n) {x y : Q} (hx : x ^ n = 1) (hy : y ^ n = 1) {r s : ℕ}
    (h : ∀ a ∈ P.map (H.bar : 𝓞 E →+* 𝓞 E) ^ r, ρ a x = 1)
    (h' : ∀ a ∈ P.map (H.bar : 𝓞 E →+* 𝓞 E) ^ s, ρ a y = 1) : e n x y 1 := by sorry
