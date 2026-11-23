-- Prove2me | Theorems.Thm_GlobalTheory_IntegralNeighbourhoodZero_isOpen_integral
-- name    : GlobalTheory.IntegralNeighbourhoodZero.isOpen_integral
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:12:59.228801+00:00
-- url     : https://prove2.me/theorems/3b1494e0-62c3-42b7-a4da-56d618d50ddc
-- title:
--   Integral Neighbourhood Zero: is Open integral
-- statement:
--   The Integral Neighbourhood Zero construction uses the is Open integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/NsmulIntegralMemNhdsZero.lean#L7-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/NsmulIntegralMemNhdsZero.lean#L7-L10

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

theorem GlobalTheory.IntegralNeighbourhoodZero.isOpen_integral (F : Type) [Field F] [NumberField F] :
    IsOpen {a : FiniteAdeleRing (RingOfIntegers F) F |
      ∀ v : HeightOneSpectrum (RingOfIntegers F), a v ∈ v.adicCompletionIntegers F} := by sorry
