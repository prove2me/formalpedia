-- Prove2me | Theorems.Thm_GlobalTheory_SS_Ord_exists_pow_mul_mem
-- name    : GlobalTheory.SS.Ord.exists_pow_mul_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:18:20.365625+00:00
-- url     : https://prove2.me/theorems/311fae03-970e-4f9e-b154-4e9b8e3ea999
-- title:
--   Ord: exists pow mul mem
-- statement:
--   The Ord construction uses the exists pow mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUniqueModelHasJacobianOrder.lean#L74-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUniqueModelHasJacobianOrder.lean#L74-L98

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

theorem GlobalTheory.SS.Ord.exists_pow_mul_mem {R B L I : Type} [CommRing R] [CommRing B] [CommRing L] [Fintype I]
    (c : R →+* B) (hc : c.FiniteType) (φ : B →+* L) (p : B) (δ : I → L →+ L)
    (hδ : ∀ i a b, δ i (a * b) = a * δ i b + b * δ i a) (h0 : ∀ i r, δ i (φ (c r)) = 0)
    (hloc : ∀ x : L, ∃ (k : ℕ) (b : B), φ b = φ p ^ k * x) :
    ∃ N : ℕ, ∀ i b, ∃ s, φ s = φ p ^ N * δ i (φ b) := by sorry
