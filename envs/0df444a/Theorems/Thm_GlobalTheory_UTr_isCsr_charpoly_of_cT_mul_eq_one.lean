-- Prove2me | Theorems.Thm_GlobalTheory_UTr_isCsr_charpoly_of_cT_mul_eq_one
-- name    : GlobalTheory.UTr.isCsr_charpoly_of_cT_mul_eq_one
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:19:57.164261+00:00
-- url     : https://prove2.me/theorems/a44ab763-8a26-44b5-9b96-18f75ceae9d5
-- title:
--   UTr: is Csr charpoly of c T mul eq one
-- statement:
--   The UTr construction uses the is Csr charpoly of c T mul eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConjugateSelfReciprocalCharpoly.lean#L10-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConjugateSelfReciprocalCharpoly.lean#L10-L39

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConjugateSelfReciprocalCharpoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix Formalism.UG
open GlobalTheory GlobalTheory.UTr

theorem GlobalTheory.UTr.isCsr_charpoly_of_cT_mul_eq_one : ∀ (R : Type) [CommRing R] (s : R →+* R) (n : ℕ)
    (M : Matrix (Fin n) (Fin n) R), cT s M * M = 1 → GlobalTheory.UTr.IsCsr s M.charpoly := by sorry
