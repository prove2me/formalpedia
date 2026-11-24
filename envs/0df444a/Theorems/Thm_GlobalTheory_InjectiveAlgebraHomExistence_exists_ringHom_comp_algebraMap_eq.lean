-- Prove2me | Theorems.Thm_GlobalTheory_InjectiveAlgebraHomExistence_exists_ringHom_comp_algebraMap_eq
-- name    : GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:19:19.156804+00:00
-- url     : https://prove2.me/theorems/dd9ca771-454c-4b6c-83a8-e93ce9e1e4cf
-- title:
--   Injective Algebra Hom Existence: exists ring Hom comp algebra Map eq
-- statement:
--   The Injective Algebra Hom Existence construction uses the exists ring Hom comp algebra Map eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRingHomCompAlgebraMapEq.lean#L16-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRingHomCompAlgebraMapEq.lean#L16-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRingHomCompAlgebraMapEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3
open GlobalTheory GlobalTheory.InjectiveAlgebraHomExistence

theorem GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq {R : Type u_1} {S : Type u_2} {K : Type u_3}
    [CommRing R] [CommRing S] [Field K] [IsAlgClosed K] [Algebra R S] [Algebra.IsIntegral R S]
    (hinj : Function.Injective (algebraMap R S)) (ψ : R →+* K) :
    ∃ x : S →+* K, x.comp (algebraMap R S) = ψ := by sorry
