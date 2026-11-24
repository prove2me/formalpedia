-- Prove2me | Theorems.Thm_GlobalTheory_SS_exists_weighted_relation
-- name    : GlobalTheory.SS.exists_weighted_relation
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:37:38.887098+00:00
-- url     : https://prove2.me/theorems/5500a380-a95b-4a32-ac4d-3b793eb944ba
-- title:
--   SS: exists weighted relation
-- statement:
--   The SS construction uses the exists weighted relation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsWeightedRelationOfMinimalSupport.lean#L56-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsWeightedRelationOfMinimalSupport.lean#L56-L138

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

theorem GlobalTheory.SS.exists_weighted_relation :
    ∀ (F T X : Type) [Field F] [Group T] (c : T → X → F) (σ : T → F →+* F) (φ : T → F) (S : Finset X) (p q : X → F), (∀ t t' χ, c (t * t') χ = c t χ * c t' χ) → (∀ χ, c 1 χ = 1) → (∀ t t' χ, σ t (c t' χ) = c t' χ) → (∀ t t', σ t (φ t') = φ (t' * t)) → (∀ t, φ t * ∑ χ ∈ S, c t χ * p χ = ∑ χ ∈ S, c t χ * q χ) → ∑ χ ∈ S, p χ ≠ 0 → ∃ (χ₀ : X) (p' q' : X → F), ∑ χ ∈ S, p' χ ≠ 0 ∧ φ 1 * ∑ χ ∈ S, p' χ = ∑ χ ∈ S, q' χ ∧ ∀ t, ∀ χ ∈ S, σ t (p' χ) * c t χ₀ = c t χ * p' χ ∧ σ t (q' χ) * c t χ₀ = c t χ * q' χ := by sorry
