-- Prove2me | Theorems.Thm_GlobalTheory_PrimeOrderScalar_sub_kill_eq
-- name    : GlobalTheory.PrimeOrderScalar.sub_kill_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-27T05:30:00.060303+00:00
-- url     : https://prove2.me/theorems/19885d84-e113-56af-bd9a-2bced7068a9d
-- title:
--   Prime Order Scalar: sub kill eq
-- statement:
--   The Prime Order Scalar construction uses the sub kill eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ActsBySameInteger.lean#L175-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ActsBySameInteger.lean#L175-L178

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ActsBySameInteger
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix
open GlobalTheory GlobalTheory.PrimeOrderScalar
open scoped TensorProduct

theorem GlobalTheory.PrimeOrderScalar.sub_kill_eq {S M : Type} [CommRing S] [AddCommGroup M] [Module S M] (P P' X X' : S)
    (hP : ∀ m : M, P • m = 0) (m : M) : ((P + P') * X) • m = (X * P' + X' * P) • m := by sorry
