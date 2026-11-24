-- Prove2me | Theorems.Thm_GlobalTheory_GaloisDescent_exists_finsupp_contract
-- name    : GlobalTheory.GaloisDescent.exists_finsupp_contract
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:42:31.014168+00:00
-- url     : https://prove2.me/theorems/e5403745-d62b-44b8-85a1-bb274bceaa0b
-- title:
--   Galois Descent: exists finsupp contract
-- statement:
--   The Galois Descent construction uses the exists finsupp contract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOneTmulOfForallFixed.lean#L157-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOneTmulOfForallFixed.lean#L157-L173

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

theorem GlobalTheory.GaloisDescent.exists_finsupp_contract (hf : IsBaseChange L f) {ι : Type*} (e : Basis ι K L) (x : M) :
    ∃ c : ι →₀ V, (∀ i, c i = contract hf (e.coord i) x) ∧ x = c.sum fun i v => e i • f v := by sorry
