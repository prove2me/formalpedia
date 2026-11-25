-- Prove2me | Theorems.Thm_GlobalTheory_AbCoh_projective_coker_of_liftsAt
-- name    : GlobalTheory.AbCoh.projective_coker_of_liftsAt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:04:53.234173+00:00
-- url     : https://prove2.me/theorems/d9b3e0b8-416f-4236-b55b-e5149dd26867
-- title:
--   Ab Coh: projective coker of lifts At
-- statement:
--   The Ab Coh construction uses the projective coker of lifts At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KrullDimLEIsLocalRingQuotPow.lean#L106-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KrullDimLEIsLocalRingQuotPow.lean#L106-L146

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KrullDimLEIsLocalRingQuotPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbCoh.LowBaseChange

theorem GlobalTheory.AbCoh.projective_coker_of_liftsAt :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (K : CochainComplex (ModuleCat.{0} R) ℕ),
      (∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) → (∃ n, ∀ p, n < p → IsZero (K.X p)) →
      (∀ i, i ≤ 2 → ∀ (R' : Type) [CommRing R'] [Algebra R R'] [IsArtinianRing R'] [IsLocalRing R']
        (k : Type) [Field k] [Algebra R k] (α : R' →ₐ[R] k), Function.Surjective α → LiftsAt K α i) →
      ∀ i, i ≤ 2 → Module.Projective R (K.X (i + 1) ⧸ LinearMap.range (K.d i (i + 1)).hom) := by sorry
