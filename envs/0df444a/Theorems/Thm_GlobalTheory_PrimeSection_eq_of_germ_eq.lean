-- Prove2me | Theorems.Thm_GlobalTheory_PrimeSection_eq_of_germ_eq
-- name    : GlobalTheory.PrimeSection.eq_of_germ_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:29:39.577073+00:00
-- url     : https://prove2.me/theorems/c7d5856e-b221-4d88-94a3-e8f5b3cb17e1
-- title:
--   Prime Section: eq of germ eq
-- statement:
--   The Prime Section construction uses the eq of germ eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqZeroOfForallPowDvdGerm.lean#L54-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqZeroOfForallPowDvdGerm.lean#L54-L60

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

theorem GlobalTheory.PrimeSection.eq_of_germ_eq {W : X.Opens} {s s' : Γ(X, W)}
    (h : ∀ hW : genericPoint X ∈ W, X.presheaf.germ W _ hW s = X.presheaf.germ W _ hW s') :
    s = s' := by sorry
