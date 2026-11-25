-- Prove2me | Theorems.Thm_GlobalTheory_PrimeSection_dvd_iff_notMem_basicOpen
-- name    : GlobalTheory.PrimeSection.dvd_iff_notMem_basicOpen
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:16:27.577355+00:00
-- url     : https://prove2.me/theorems/171a9661-659c-5218-98fd-c2d93eb14303
-- title:
--   Prime Section: dvd iff not Mem basic Open
-- statement:
--   The Prime Section construction uses the dvd iff not Mem basic Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqZeroOfForallPowDvdGerm.lean#L158-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqZeroOfForallPowDvdGerm.lean#L158-L161

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqZeroOfForallPowDvdGerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.PrimeSection
variable {X : Scheme.{u}} {t : Γ(X, ⊤)} {η : X}
  (hη : ∀ x : X, x ∉ X.basicOpen t ↔ η ⤳ x)
  (hp : ∀ U : X.Opens, IsAffineOpen U → η ∈ U →
    Prime (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t))
include hη hp

theorem GlobalTheory.PrimeSection.dvd_iff_notMem_basicOpen {U : X.Opens} (hU : IsAffineOpen U) (h : η ∈ U) (s : Γ(X, U)) :
    X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t ∣ s ↔ η ∉ X.basicOpen s := by sorry
