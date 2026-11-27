-- Prove2me | Theorems.Thm_GlobalTheory_PrimeOrderScalar_zsmul_eq_zero_iff
-- name    : GlobalTheory.PrimeOrderScalar.zsmul_eq_zero_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-27T05:30:03.605241+00:00
-- url     : https://prove2.me/theorems/a04ab003-b725-51a7-a173-238ae93d9a3a
-- title:
--   Prime Order Scalar: zsmul eq zero iff
-- statement:
--   The Prime Order Scalar construction uses the zsmul eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ActsBySameInteger.lean#L14-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ActsBySameInteger.lean#L14-L37

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

theorem GlobalTheory.PrimeOrderScalar.zsmul_eq_zero_iff (hT : T.Prime) (hM : Nat.card M = T) (n : ℤ) :
    (∀ m : M, n • m = 0) ↔ (T : ℤ) ∣ n := by sorry
