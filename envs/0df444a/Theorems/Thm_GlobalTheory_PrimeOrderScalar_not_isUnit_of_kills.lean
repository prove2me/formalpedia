-- Prove2me | Theorems.Thm_GlobalTheory_PrimeOrderScalar_not_isUnit_of_kills
-- name    : GlobalTheory.PrimeOrderScalar.not_isUnit_of_kills
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-27T05:31:06.089833+00:00
-- url     : https://prove2.me/theorems/f5512b77-9e87-4dcd-9c0d-4c59f5e10946
-- title:
--   Prime Order Scalar: not is Unit of kills
-- statement:
--   The Prime Order Scalar construction uses the not is Unit of kills property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ActsBySameInteger.lean#L49-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ActsBySameInteger.lean#L49-L56

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
variable {S M : Type} [CommRing S] [AddCommGroup M] [Module S M] {T : ℕ}

theorem GlobalTheory.PrimeOrderScalar.not_isUnit_of_kills (hT : T.Prime) (hM : Nat.card M = T) {u : S}
    (hu : ∀ m : M, u • m = 0) : ¬ IsUnit u := by sorry
