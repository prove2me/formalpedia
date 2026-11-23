-- Prove2me | Theorems.Thm_GlobalTheory_IntegralOpen_isOpen_integral
-- name    : GlobalTheory.IntegralOpen.isOpen_integral
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:45.123666+00:00
-- url     : https://prove2.me/theorems/4248c700-f826-4e2a-b78b-e2b12ee96afd
-- title:
--   Integral Open: is Open integral
-- statement:
--   The Integral Open construction uses the is Open integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ImportsBis.lean#L7-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ImportsBis.lean#L7-L15

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ImportsBis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntegralOpen
open IsDedekindDomain NumberField

theorem GlobalTheory.IntegralOpen.isOpen_integral (F : Type) [Field F] [NumberField F] :
    IsOpen {a : FiniteAdeleRing (RingOfIntegers F) F |
      ∀ v : HeightOneSpectrum (RingOfIntegers F),
        (a : (w : HeightOneSpectrum (RingOfIntegers F)) → HeightOneSpectrum.adicCompletion F w) v ∈
          HeightOneSpectrum.adicCompletionIntegers F v} := by sorry
