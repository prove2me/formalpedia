-- Prove2me | Theorems.Thm_GlobalTheory_SmallPoint_exists_eventually_norm_le
-- name    : GlobalTheory.SmallPoint.exists_eventually_norm_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:15:31.67104+00:00
-- url     : https://prove2.me/theorems/84b330c2-23eb-45eb-8477-a3fd517c0e30
-- title:
--   Small Point: exists eventually norm le
-- statement:
--   The Small Point construction uses the exists eventually norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsComplexPointNormLtOfNotIsUnit.lean#L60-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsComplexPointNormLtOfNotIsUnit.lean#L60-L86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SpecialisationNumberFieldAndCountableValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowCardLeNormProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsComplexPointNormLtOfNotIsUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Topology
open GlobalTheory
open GlobalTheory.SmallPoint

theorem GlobalTheory.SmallPoint.exists_eventually_norm_le {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (Ψ : R →+* ℂ[X]) {b : B} (hb : IsIntegral R b) :
    ∃ M : ℝ, ∀ᶠ s in 𝓝 (0 : ℂ), ∀ φ : B →+* ℂ,
      φ.comp (algebraMap R B) = (evalRingHom s).comp Ψ → ‖φ b‖ ≤ M := by sorry
