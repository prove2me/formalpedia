-- Prove2me | Theorems.Thm_GlobalTheory_LocalNormBound_main
-- name    : GlobalTheory.LocalNormBound.main
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:39:42.218539+00:00
-- url     : https://prove2.me/theorems/cff9d416-4392-48e4-8e5c-ec27c8d98de7
-- title:
--   Local Norm Bound: main
-- statement:
--   The Local Norm Bound construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ImportsTer.lean#L30-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ImportsTer.lean#L30-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ImportsTer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField Filter Topology
open GlobalTheory GlobalTheory.LocalNormBound

theorem GlobalTheory.LocalNormBound.main : ∀ (F : Type) [inst : Field F] [inst_1 : NumberField F], ∀ U ∈ nhds (0 : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F), ∃ (N : ℕ), (0 : ℕ) < N ∧ ∀ (a : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F), (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), (a : (a : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) → IsDedekindDomain.HeightOneSpectrum.adicCompletion F a) v ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v) → N • a ∈ U := by sorry
