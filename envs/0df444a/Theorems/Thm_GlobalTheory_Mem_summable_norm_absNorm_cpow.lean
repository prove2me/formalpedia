-- Prove2me | Theorems.Thm_GlobalTheory_Mem_summable_norm_absNorm_cpow
-- name    : GlobalTheory.Mem.summable_norm_absNorm_cpow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:27.071185+00:00
-- url     : https://prove2.me/theorems/62345fd0-ce9e-473e-a222-c4e8ebf52157
-- title:
--   Mem: summable norm abs Norm cpow
-- statement:
--   The Mem construction uses the summable norm abs Norm cpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RayLSeriesEulerProduct.lean#L114-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RayLSeriesEulerProduct.lean#L114-L129

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex Filter Topology
open scoped ComplexOrder
open GlobalTheory GlobalTheory.Mem

theorem GlobalTheory.Mem.summable_norm_absNorm_cpow (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    Summable fun I : Ideal (𝓞 K) => ‖((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)‖ := by sorry
