-- Prove2me | Theorems.Thm_GlobalTheory_PrimeOrderScalar_int_dvd_of_mem
-- name    : GlobalTheory.PrimeOrderScalar.int_dvd_of_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-27T05:30:17.503895+00:00
-- url     : https://prove2.me/theorems/6b344363-c537-5100-8ba0-ef541b848c3b
-- title:
--   Prime Order Scalar: int dvd of mem
-- statement:
--   The Prime Order Scalar construction uses the int dvd of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ActsBySameInteger.lean#L58-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ActsBySameInteger.lean#L58-L67

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

theorem GlobalTheory.PrimeOrderScalar.int_dvd_of_mem {R : Type} [CommRing R] {I : Ideal R} (hI : I ≠ ⊤) (hT : T.Prime)
    (hTI : (T : R) ∈ I) {n : ℤ} (hn : (n : R) ∈ I) : (T : ℤ) ∣ n := by sorry
