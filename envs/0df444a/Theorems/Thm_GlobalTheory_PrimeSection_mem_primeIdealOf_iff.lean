-- Prove2me | Theorems.Thm_GlobalTheory_PrimeSection_mem_primeIdealOf_iff
-- name    : GlobalTheory.PrimeSection.mem_primeIdealOf_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:29:24.645717+00:00
-- url     : https://prove2.me/theorems/e8486038-1809-401a-a037-d18bedfc3368
-- title:
--   Prime Section: mem prime Ideal Of iff
-- statement:
--   The Prime Section construction uses the mem prime Ideal Of iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqZeroOfForallPowDvdGerm.lean#L115-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqZeroOfForallPowDvdGerm.lean#L115-L119

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

theorem GlobalTheory.PrimeSection.mem_primeIdealOf_iff {U : X.Opens} (hU : IsAffineOpen U) (x : U) (s : Γ(X, U)) :
    s ∈ (hU.primeIdealOf x).asIdeal ↔ x.1 ∉ X.basicOpen s := by sorry
