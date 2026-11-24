-- Prove2me | Theorems.Thm_GlobalTheory_OnePoint_existsUnique_section
-- name    : GlobalTheory.OnePoint.existsUnique_section
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:37:49.366906+00:00
-- url     : https://prove2.me/theorems/31fdebda-2fed-4250-9f09-99e840d1877f
-- title:
--   One Point: exists Unique section
-- statement:
--   The One Point construction uses the exists Unique section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegrallyClosedInFractionFieldPowerSeries.lean#L218-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegrallyClosedInFractionFieldPowerSeries.lean#L218-L229

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsIntegrallyClosedInFractionFieldPowerSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped LaurentSeries PowerSeries
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.OnePoint
universe u v w
local notation "specAlg(" K ", " L ")" => Spec.map (CommRingCat.ofHom (algebraMap K L))
variable {K : Type u} [Field K]

theorem GlobalTheory.OnePoint.existsUnique_section [PerfectField K] {F : Scheme.{u}} [Nonempty F]
    (f : F ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    (h : ∀ a b : Spec (.of Ω) ⟶ F, a ≫ f = specAlg(K, Ω) → b ≫ f = specAlg(K, Ω) → a = b) :
    ∃ s : Spec (.of K) ⟶ F, s ≫ f = 𝟙 _ ∧ (∀ s' : Spec (.of K) ⟶ F, s' ≫ f = 𝟙 _ → s' = s) ∧
      ∀ (T : Scheme.{u}) [IsReduced T] (t : T ⟶ F), (t ≫ f) ≫ s = t := by sorry
