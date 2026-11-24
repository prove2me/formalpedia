-- Prove2me | Theorems.Thm_GlobalTheory_CoprimeBasis_isCoprime_of_mem_primeTo
-- name    : GlobalTheory.CoprimeBasis.isCoprime_of_mem_primeTo
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:27:27.030025+00:00
-- url     : https://prove2.me/theorems/4b04fad7-4145-4b33-b6b1-cc1796d8a472
-- title:
--   Coprime Basis: is Coprime of mem prime To
-- statement:
--   The Coprime Basis construction uses the is Coprime of mem prime To property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIndependentBasisCoprime.lean#L20-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIndependentBasisCoprime.lean#L20-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemLocDIffSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIndependentBasisCoprime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.CoprimeBasis

theorem GlobalTheory.CoprimeBasis.isCoprime_of_mem_primeTo {R : Type} [CommRing R] {s d : R}
    (hs : s ∈ GlobalTheory.Mass.primeTo d) : IsCoprime s d := by sorry
