-- Prove2me | Theorems.Thm_GlobalTheory_linearIndepOn_pow_of_isDomain_tensor_purelyInseparable
-- name    : GlobalTheory.linearIndepOn_pow_of_isDomain_tensor_purelyInseparable
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:07:08.0078+00:00
-- url     : https://prove2.me/theorems/554d16c7-d0e7-43fd-8d3f-3b1d0f245e0f
-- title:
--   Global Theory: linear Indep On pow of is Domain tensor purely Inseparable
-- statement:
--   The Global Theory construction uses the linear Indep On pow of is Domain tensor purely Inseparable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LinearIndepOnPowOfIsDomainTensorPurelyInseparabl.lean#L6-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LinearIndepOnPowOfIsDomainTensorPurelyInseparabl.lean#L6-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndepOnPowOfIsDomainTensorPurelyInseparabl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory

theorem GlobalTheory.linearIndepOn_pow_of_isDomain_tensor_purelyInseparable (k B : Type) [Field k] [CommRing B]
    [IsDomain B] [Algebra k B] (p : ℕ) (hp : p.Prime) (hk : CharP k p)
    (hdom : ∀ (K : Type) [Field K] [Algebra k K], FiniteDimensional k K →
      IsPurelyInseparable k K → IsDomain (K ⊗[k] B))
    (s : Finset (FractionRing B)) (hs : LinearIndepOn k _root_.id (s : Set (FractionRing B))) :
    LinearIndepOn k (· ^ p) (s : Set (FractionRing B)) := by sorry
