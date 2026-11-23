-- Prove2me | Theorems.Thm_GlobalTheory_GaloisDescent_contract_smul
-- name    : GlobalTheory.GaloisDescent.contract_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:51:44.491706+00:00
-- url     : https://prove2.me/theorems/89116702-8b62-48d1-91f9-96ca73bef48e
-- title:
--   Galois Descent: contract smul
-- statement:
--   The Galois Descent construction uses the contract smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOneTmulOfForallFixed.lean#L135-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOneTmulOfForallFixed.lean#L135-L137

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

theorem GlobalTheory.GaloisDescent.contract_smul (hf : IsBaseChange L f) (l : L →ₗ[K] K) (a : L) (v : V) :
    contract hf l (a • f v) = l a • v := by sorry
