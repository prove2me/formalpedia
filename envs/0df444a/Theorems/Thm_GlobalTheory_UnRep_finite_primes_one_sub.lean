-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_finite_primes_one_sub
-- name    : GlobalTheory.UnRep.finite_primes_one_sub
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:24:12.237837+00:00
-- url     : https://prove2.me/theorems/6cb455dc-d66c-451f-bc11-fb4e2b3941f4
-- title:
--   Un Rep: finite primes one sub
-- statement:
--   The Un Rep construction uses the finite primes one sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/AdelicUnitaryScalingUnit.lean#L89-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/AdelicUnitaryScalingUnit.lean#L89-L110

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormOneInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_AdelicUnitaryScalingUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep

theorem GlobalTheory.UnRep.finite_primes_one_sub (F : Type) [Field F] [NumberField F] (e : FiniteAdeleRing (𝓞 F) F)
    (he : {v | e v ≠ 0}.Finite) :
    {P : Ideal (FiniteAdeleRing (𝓞 F) F) | P.IsPrime ∧ 1 - e ∈ P}.Finite := by sorry
