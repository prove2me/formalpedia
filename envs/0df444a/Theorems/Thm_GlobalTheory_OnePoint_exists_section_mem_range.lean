-- Prove2me | Theorems.Thm_GlobalTheory_OnePoint_exists_section_mem_range
-- name    : GlobalTheory.OnePoint.exists_section_mem_range
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:37:33.044667+00:00
-- url     : https://prove2.me/theorems/949fb113-b455-4cc4-8bfa-8bd5e6f95744
-- title:
--   One Point: exists section mem range
-- statement:
--   The One Point construction uses the exists section mem range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegrallyClosedInFractionFieldPowerSeries.lean#L152-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegrallyClosedInFractionFieldPowerSeries.lean#L152-L181

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

theorem GlobalTheory.OnePoint.exists_section_mem_range [PerfectField K] {F : Scheme.{u}} (f : F ⟶ Spec (.of K))
    [LocallyOfFiniteType f] (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    (h : ∀ a b : Spec (.of Ω) ⟶ F, a ≫ f = specAlg(K, Ω) → b ≫ f = specAlg(K, Ω) → a = b)
    (p : F) : ∃ s : Spec (.of K) ⟶ F, s ≫ f = 𝟙 _ ∧ p ∈ Set.range s := by sorry
