-- Prove2me | Theorems.Thm_GlobalTheory_PrimeSection_primeIdealOf_eq_span
-- name    : GlobalTheory.PrimeSection.primeIdealOf_eq_span
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:28:58.783288+00:00
-- url     : https://prove2.me/theorems/fa2b0e4d-9cb5-4756-bdef-b7489656d3b9
-- title:
--   Prime Section: prime Ideal Of eq span
-- statement:
--   The Prime Section construction uses the prime Ideal Of eq span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqZeroOfForallPowDvdGerm.lean#L123-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqZeroOfForallPowDvdGerm.lean#L123-L154

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

theorem GlobalTheory.PrimeSection.primeIdealOf_eq_span {U : X.Opens} (hU : IsAffineOpen U) (h : η ∈ U) :
    (hU.primeIdealOf ⟨η, h⟩).asIdeal =
      Ideal.span {X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t} := by sorry
