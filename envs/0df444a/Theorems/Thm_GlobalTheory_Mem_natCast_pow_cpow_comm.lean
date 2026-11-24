-- Prove2me | Theorems.Thm_GlobalTheory_Mem_natCast_pow_cpow_comm
-- name    : GlobalTheory.Mem.natCast_pow_cpow_comm
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:24:44.365545+00:00
-- url     : https://prove2.me/theorems/1a38319f-e1d5-45a0-afdf-d0e8baff4c94
-- title:
--   Mem: nat Cast pow cpow comm
-- statement:
--   The Mem construction uses the nat Cast pow cpow comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DedekindZetaFactorizationRay.lean#L155-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DedekindZetaFactorizationRay.lean#L155-L156

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProductStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DedekindZetaFactorizationRay
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
open GlobalTheory GlobalTheory.Mem

theorem GlobalTheory.Mem.natCast_pow_cpow_comm (q k : ℕ) (z : ℂ) : ((q : ℂ) ^ k) ^ z = ((q : ℂ) ^ z) ^ k := by sorry
