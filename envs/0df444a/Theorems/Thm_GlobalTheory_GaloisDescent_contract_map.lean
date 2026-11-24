-- Prove2me | Theorems.Thm_GlobalTheory_GaloisDescent_contract_map
-- name    : GlobalTheory.GaloisDescent.contract_map
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:43:25.174995+00:00
-- url     : https://prove2.me/theorems/583bc017-697a-4c93-b4eb-54edfe6059d7
-- title:
--   Galois Descent: contract map
-- statement:
--   The Galois Descent construction uses the contract map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOneTmulOfForallFixed.lean#L217-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOneTmulOfForallFixed.lean#L217-L225

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOneTmulOfForallFixed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
open GlobalTheory GlobalTheory.GaloisDescent
variable {K L V M G : Type*} [Field K] [Field L] [Algebra K L] [AddCommGroup V] [Module K V]
  [AddCommGroup M] [Module K M] [Module L M] [IsScalarTower K L M] {f : V →ₗ[K] M}
variable {V' M' : Type*} [AddCommGroup V'] [Module K V']
  [AddCommGroup M'] [Module K M'] [Module L M'] [IsScalarTower K L M'] {f' : V' →ₗ[K] M'}

theorem GlobalTheory.GaloisDescent.contract_map (hf : IsBaseChange L f) (hf' : IsBaseChange L f') (p : V →ₗ[K] V')
    (F : M →ₗ[L] M') (hF : ∀ v, F (f v) = f' (p v)) (l : L →ₗ[K] K) (x : M) :
    contract hf' l (F x) = p (contract hf l x) := by sorry
