-- Prove2me | Theorems.Thm_GlobalTheory_IsHilbertPoly_coker
-- name    : GlobalTheory.IsHilbertPoly.coker
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:11:09.959007+00:00
-- url     : https://prove2.me/theorems/62b1f8c6-1e09-5482-b4ce-075527adf3df
-- title:
--   Is Hilbert Poly: coker
-- statement:
--   The Is Hilbert Poly construction uses the coker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/XSmulMemWeightedHomogeneousSubmodule.lean#L606-L627
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/XSmulMemWeightedHomogeneousSubmodule.lean#L606-L627

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

theorem GlobalTheory.IsHilbertPoly.coker {ℳ' : ℤ → Submodule k M'} [Decomposition ℳ']
    {ℳ : ℤ → Submodule k M} [Decomposition ℳ] {P' P : ℚ[X]} (hP' : IsHilbertPoly ℳ' P')
    (hP : IsHilbertPoly ℳ P) (f : M' →ₗ[k] M) (g : M →ₗ[k] M'') (d : ℤ)
    (hf : ∀ n, ∀ m ∈ ℳ' n, f m ∈ ℳ (n + d)) (hinj : Function.Injective f)
    (hfg : Function.Exact f g) :
    IsHilbertPoly (fun n => (ℳ n).map g) (P - P'.comp (X - C (d : ℚ))) := by sorry
