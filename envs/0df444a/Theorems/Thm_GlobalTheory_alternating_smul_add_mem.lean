-- Prove2me | Theorems.Thm_GlobalTheory_alternating_smul_add_mem
-- name    : GlobalTheory.alternating_smul_add_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:11:45.056261+00:00
-- url     : https://prove2.me/theorems/44abe9b2-ea7c-4a50-b1ba-e58b4095a825
-- title:
--   Global Theory: alternating smul add mem
-- statement:
--   The Global Theory construction uses the alternating smul add mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L14-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L14-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped BigOperators TensorProduct nonZeroDivisors
open Module KaehlerDifferential IsLocalRing
variable {R M N ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.alternating_smul_add_mem (ω : M [⋀^ι]→ₗ[R] N) (P : Submodule R N) (θ : M) (a : ι → R)
    (w : ι → M) (h₀ : ω w ∈ P) (h₁ : ∀ i, ω (Function.update w i θ) ∈ P) :
    ω (fun i => a i • θ + w i) ∈ P := by sorry
