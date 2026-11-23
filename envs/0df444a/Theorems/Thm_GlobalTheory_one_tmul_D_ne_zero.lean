-- Prove2me | Theorems.Thm_GlobalTheory_one_tmul_D_ne_zero
-- name    : GlobalTheory.one_tmul_D_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:23.774815+00:00
-- url     : https://prove2.me/theorems/e05dfa4d-df54-43ba-9172-322034b45acc
-- title:
--   Global Theory: one tmul D ne zero
-- statement:
--   The Global Theory construction uses the one tmul D ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L477-L497
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L477-L497

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
variable (K : Type*) {V : Type*} [Field K] [PerfectField K] [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V] [Algebra K V] [Algebra.EssFiniteType K V]
  [Algebra.FormallySmooth K V]

theorem GlobalTheory.one_tmul_D_ne_zero {t : V} (ht : Irreducible t) :
    (1 : ResidueField V) ⊗ₜ[V] D K V t ≠ 0 := by sorry
