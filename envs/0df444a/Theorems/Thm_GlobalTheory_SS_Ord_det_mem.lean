-- Prove2me | Theorems.Thm_GlobalTheory_SS_Ord_det_mem
-- name    : GlobalTheory.SS.Ord.det_mem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:17:10.981291+00:00
-- url     : https://prove2.me/theorems/95f1c60a-1d3d-4b7c-bdb3-10653b05f5c9
-- title:
--   Ord: det mem
-- statement:
--   The Ord construction uses the det mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUniqueModelHasJacobianOrder.lean#L42-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUniqueModelHasJacobianOrder.lean#L42-L72

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelHasJacobianOrder
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
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Ord

theorem GlobalTheory.SS.Ord.det_mem {B S L I : Type} [CommRing B] [CommRing S] [CommRing L] [Fintype I] [DecidableEq I]
    (ρ : B →+* S) (φ : S →+* L) (δ : I → L →+ L) (hδ : ∀ i a b, δ i (a * b) = a * δ i b + b * δ i a)
    (hloc : ∀ x : S, ∃ (b c : B), IsUnit (ρ c) ∧ x * ρ c = ρ b)
    (N : AddSubgroup L) (hN : ∀ s : S, ∀ x ∈ N, φ s * x ∈ N)
    (h : ∀ t : I → B, (Matrix.of fun i j => δ i (φ (ρ (t j)))).det ∈ N) (t : I → S) :
    (Matrix.of fun i j => δ i (φ (t j))).det ∈ N := by sorry
