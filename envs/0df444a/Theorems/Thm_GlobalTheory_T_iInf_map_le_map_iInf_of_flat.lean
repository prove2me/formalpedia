-- Prove2me | Theorems.Thm_GlobalTheory_T_iInf_map_le_map_iInf_of_flat
-- name    : GlobalTheory.T.iInf_map_le_map_iInf_of_flat
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:33:12.23554+00:00
-- url     : https://prove2.me/theorems/a483f9ac-ddf9-4aa2-8547-7b96eb0e4ed1
-- title:
--   T: i Inf map le map i Inf of flat
-- statement:
--   The T construction uses the i Inf map le map i Inf of flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IInfMapLeMapIInfOfFlatStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IInfMapLeMapIInfOfFlatStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IInfMapLeMapIInfOfFlat
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IInfMapLeMapIInfOfFlatStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.iInf_map_le_map_iInf_of_flat : ∀ {B R : Type} [CommRing B] [CommRing R] [Algebra B R] [Module.Flat B R] {ι : Type} [Finite ι] (K : ι → Ideal B), ⨅ i, (K i).map (algebraMap B R) ≤ (⨅ i, K i).map (algebraMap B R) := by sorry
