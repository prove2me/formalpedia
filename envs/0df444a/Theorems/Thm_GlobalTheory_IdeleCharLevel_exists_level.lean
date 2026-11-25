-- Prove2me | Theorems.Thm_GlobalTheory_IdeleCharLevel_exists_level
-- name    : GlobalTheory.IdeleCharLevel.exists_level
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:08:23.234699+00:00
-- url     : https://prove2.me/theorems/501fa32a-1f95-5983-9274-a78bed7f0f25
-- title:
--   Idele Char Level: exists level
-- statement:
--   The Idele Char Level construction uses the exists level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IdeleCongruenceUnitCriterion.lean#L11-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IdeleCongruenceUnitCriterion.lean#L11-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdeleCongruenceUnitCriterion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors Topology
open GlobalTheory GlobalTheory.IdeleCharLevel
variable (K : Type) [Field K] [NumberField K]

theorem GlobalTheory.IdeleCharLevel.exists_level (U : Set (FiniteAdeleRing (𝓞 K) K)) (hU : U ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 K) K)) :
    ∃ M : ℕ, M ≠ 0 ∧ ∀ a : FiniteAdeleRing (𝓞 K) K,
      (∀ P : HeightOneSpectrum (𝓞 K), Valued.v (a P) ≤ P.intValuation (M : 𝓞 K)) → a ∈ U := by sorry
