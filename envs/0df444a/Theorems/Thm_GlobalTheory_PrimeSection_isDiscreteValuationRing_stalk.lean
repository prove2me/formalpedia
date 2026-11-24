-- Prove2me | Theorems.Thm_GlobalTheory_PrimeSection_isDiscreteValuationRing_stalk
-- name    : GlobalTheory.PrimeSection.isDiscreteValuationRing_stalk
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:29:23.593513+00:00
-- url     : https://prove2.me/theorems/ef3e6590-c4f3-40c3-8e6d-ee3c7e3277aa
-- title:
--   Prime Section: is Discrete Valuation Ring stalk
-- statement:
--   The Prime Section construction uses the is Discrete Valuation Ring stalk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqZeroOfForallPowDvdGerm.lean#L167-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqZeroOfForallPowDvdGerm.lean#L167-L185

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
variable [IsIntegral X]
include hη hp

theorem GlobalTheory.PrimeSection.isDiscreteValuationRing_stalk [IsLocallyNoetherian X] :
    IsDiscreteValuationRing (X.presheaf.stalk η) ∧
      Irreducible (X.presheaf.germ ⊤ η trivial t) := by sorry
