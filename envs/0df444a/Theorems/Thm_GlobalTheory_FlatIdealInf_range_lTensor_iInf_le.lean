-- Prove2me | Theorems.Thm_GlobalTheory_FlatIdealInf_range_lTensor_iInf_le
-- name    : GlobalTheory.FlatIdealInf.range_lTensor_iInf_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:32:40.949501+00:00
-- url     : https://prove2.me/theorems/7ffb4cba-8239-4573-8d27-db1fa5e8012f
-- title:
--   Flat Ideal Inf: range l Tensor i Inf le
-- statement:
--   The Flat Ideal Inf construction uses the range l Tensor i Inf le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IInfMapLeMapIInfOfFlat.lean#L8-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IInfMapLeMapIInfOfFlat.lean#L8-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IInfMapLeMapIInfOfFlat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.FlatIdealInf
open TensorProduct

theorem GlobalTheory.FlatIdealInf.range_lTensor_iInf_le {B R M : Type} [CommRing B] [AddCommGroup R] [Module B R]
    [Module.Flat B R] [AddCommGroup M] [Module B M] {ι : Type} [Finite ι]
    (K : ι → Submodule B M) :
    ⨅ i, LinearMap.range (LinearMap.lTensor R (K i).subtype) ≤
      LinearMap.range (LinearMap.lTensor R (⨅ i, K i).subtype) := by sorry
