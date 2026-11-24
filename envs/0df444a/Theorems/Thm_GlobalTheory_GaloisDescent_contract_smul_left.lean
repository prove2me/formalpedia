-- Prove2me | Theorems.Thm_GlobalTheory_GaloisDescent_contract_smul_left
-- name    : GlobalTheory.GaloisDescent.contract_smul_left
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:43:15.474651+00:00
-- url     : https://prove2.me/theorems/7899be96-ebb8-4276-9ee3-59b3d1b514cd
-- title:
--   Galois Descent: contract smul left
-- statement:
--   The Galois Descent construction uses the contract smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOneTmulOfForallFixed.lean#L147-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOneTmulOfForallFixed.lean#L147-L155

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

theorem GlobalTheory.GaloisDescent.contract_smul_left (hf : IsBaseChange L f) (l : L →ₗ[K] K) (a : L) (x : M) :
    contract hf l (a • x) = contract hf (l ∘ₗ LinearMap.mulLeft K a) x := by sorry
