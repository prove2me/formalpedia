-- Prove2me | Theorems.Thm_GlobalTheory_HeckeCompare_conj_isMaximal
-- name    : GlobalTheory.HeckeCompare.conj_isMaximal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:53.733803+00:00
-- url     : https://prove2.me/theorems/16bc90f5-0741-4bd1-8c76-de2efbbb716a
-- title:
--   Hecke Compare: conj is Maximal
-- statement:
--   The Hecke Compare construction uses the conj is Maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NatCastMemConj.lean#L249-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NatCastMemConj.lean#L249-L250

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

theorem GlobalTheory.HeckeCompare.conj_isMaximal (H : Host E) (P : Ideal (𝓞 E)) [P.IsMaximal] : (P.map (H.bar : 𝓞 E →+* 𝓞 E)).IsMaximal := by sorry
