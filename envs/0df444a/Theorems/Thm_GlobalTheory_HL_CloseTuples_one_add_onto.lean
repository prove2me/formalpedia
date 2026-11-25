-- Prove2me | Theorems.Thm_GlobalTheory_HL_CloseTuples_one_add_onto
-- name    : GlobalTheory.HL.CloseTuples.one_add_onto
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:10:49.004726+00:00
-- url     : https://prove2.me/theorems/90c6adab-ff35-4ebc-b189-5e858c2e3f0a
-- title:
--   Close Tuples: one add onto
-- statement:
--   The Close Tuples construction uses the one add onto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsIsometryNearIdentityCloseTuples.lean#L54-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsIsometryNearIdentityCloseTuples.lean#L54-L73

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DualInterSelfDualHermitianLatticeSubspace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryNearIdentityCloseTuples
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CloseTuples
open GlobalTheory.HL.Eichler GlobalTheory.HL.DualInter
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E}

theorem GlobalTheory.HL.CloseTuples.one_add_onto {Λ : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) (p : L.O)
    (hp : p ∈ Ideal.jacobson (⊥ : Ideal L.O)) (A : (Fin n → E) →ₗ[E] (Fin n → E))
    (hA : ∀ v ∈ Λ, A v ∈ Λ) :
    Function.Bijective (LinearMap.id + (p : E) • A : (Fin n → E) →ₗ[E] (Fin n → E)) ∧
      ∀ v ∈ Λ, ∃ u ∈ Λ, u + (p : E) • A u = v := by sorry
