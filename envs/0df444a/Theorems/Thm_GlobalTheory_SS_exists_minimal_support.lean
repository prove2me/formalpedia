-- Prove2me | Theorems.Thm_GlobalTheory_SS_exists_minimal_support
-- name    : GlobalTheory.SS.exists_minimal_support
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:39:16.314661+00:00
-- url     : https://prove2.me/theorems/e8de966a-a04e-4f01-8920-238675a5293b
-- title:
--   SS: exists minimal support
-- statement:
--   The SS construction uses the exists minimal support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsWeightedRelationOfMinimalSupport.lean#L12-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsWeightedRelationOfMinimalSupport.lean#L12-L54

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsUnitEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsWeightedRelationOfMinimalSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.SS

theorem GlobalTheory.SS.exists_minimal_support {F J : Type} [Field F] (A : Finset J) (M : (J → F) → Prop)
    (L : (J → F) → F) (hM : ∀ v w (a : F), M v → M w → M (fun i => v i - a * w i))
    (hL : ∀ v w (a : F), L (fun i => v i - a * w i) = L v - a * L w)
    (v : J → F) (hv : M v) (hLv : L v ≠ 0) :
    ∃ v', M v' ∧ L v' ≠ 0 ∧ ∀ w, M w → (∀ i ∈ A, v' i = 0 → w i = 0) →
      ∀ i₀ ∈ A, v' i₀ ≠ 0 → w i₀ = 0 → ∀ i ∈ A, w i = 0 := by sorry
