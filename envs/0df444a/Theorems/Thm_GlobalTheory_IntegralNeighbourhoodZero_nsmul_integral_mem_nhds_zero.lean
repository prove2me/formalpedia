-- Prove2me | Theorems.Thm_GlobalTheory_IntegralNeighbourhoodZero_nsmul_integral_mem_nhds_zero
-- name    : GlobalTheory.IntegralNeighbourhoodZero.nsmul_integral_mem_nhds_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:20:50.102806+00:00
-- url     : https://prove2.me/theorems/51c7a74a-9af6-4781-aaf9-1b866f2bc55f
-- title:
--   Integral Neighbourhood Zero: nsmul integral mem nhds zero
-- statement:
--   The Integral Neighbourhood Zero construction uses the nsmul integral mem nhds zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/NsmulIntegralMemNhdsZero.lean#L12-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/NsmulIntegralMemNhdsZero.lean#L12-L35

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_NsmulIntegralMemNhdsZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntegralNeighbourhoodZero
open IsDedekindDomain NumberField

theorem GlobalTheory.IntegralNeighbourhoodZero.nsmul_integral_mem_nhds_zero (F : Type) [Field F] [NumberField F] (M : ℕ) (hM : 0 < M) :
    {c : FiniteAdeleRing (RingOfIntegers F) F |
      ∃ a : FiniteAdeleRing (RingOfIntegers F) F,
        (∀ v : HeightOneSpectrum (RingOfIntegers F), a v ∈ v.adicCompletionIntegers F) ∧
          c = M • a} ∈ nhds (0 : FiniteAdeleRing (RingOfIntegers F) F) := by sorry
