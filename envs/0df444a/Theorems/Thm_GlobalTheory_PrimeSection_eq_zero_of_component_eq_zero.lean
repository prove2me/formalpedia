-- Prove2me | Theorems.Thm_GlobalTheory_PrimeSection_eq_zero_of_component_eq_zero
-- name    : GlobalTheory.PrimeSection.eq_zero_of_component_eq_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:29:02.677303+00:00
-- url     : https://prove2.me/theorems/b803d456-a40f-4e13-b4cc-11cbe14f5f43
-- title:
--   Prime Section: eq zero of component eq zero
-- statement:
--   The Prime Section construction uses the eq zero of component eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqZeroOfForallPowDvdGerm.lean#L69-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqZeroOfForallPowDvdGerm.lean#L69-L76

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
variable {X : Scheme.{u}} [IsIntegral X]

theorem GlobalTheory.PrimeSection.eq_zero_of_component_eq_zero {ι : Type v} {U : ι → X.Opens}
    (g : ∀ a b, Γ(X, U a ⊓ U b)) (s : ∀ a, Γ(X, U a))
    (hs : ∀ a b, X.presheaf.map (homOfLE inf_le_left).op (s a) =
      g a b * X.presheaf.map (homOfLE inf_le_right).op (s b))
    {a : ι} {x : X} (hx : x ∈ U a) (h : s a = 0) (b : ι) : s b = 0 := by sorry
