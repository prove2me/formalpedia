-- Prove2me | Theorems.Thm_GlobalTheory_finrank_eq_add_of_exact
-- name    : GlobalTheory.finrank_eq_add_of_exact
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:47:30.615826+00:00
-- url     : https://prove2.me/theorems/498b1e22-8aa8-49b0-95b6-652a93db725a
-- title:
--   Global Theory: finrank eq add of exact
-- statement:
--   The Global Theory construction uses the finrank eq add of exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/XSmulMemWeightedHomogeneousSubmodule.lean#L592-L604
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/XSmulMemWeightedHomogeneousSubmodule.lean#L592-L604

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter
open GlobalTheory
open DirectSum Module GradedHilbert
variable {k : Type*} [Field k] {M' M M'' : Type*} [AddCommGroup M'] [Module k M']
  [AddCommGroup M] [Module k M] [AddCommGroup M''] [Module k M'']

theorem GlobalTheory.finrank_eq_add_of_exact (ℳ' : ℤ → Submodule k M') [Decomposition ℳ']
    (ℳ : ℤ → Submodule k M) [Decomposition ℳ] (f : M' →ₗ[k] M) (g : M →ₗ[k] M'') (d : ℤ)
    (hf : ∀ n, ∀ m ∈ ℳ' n, f m ∈ ℳ (n + d)) (hinj : Function.Injective f)
    (hfg : Function.Exact f g) (n : ℤ) [Module.Finite k (ℳ (n + d))] :
    finrank k (ℳ (n + d)) = finrank k (ℳ' n) + finrank k ((ℳ (n + d)).map g) := by sorry
