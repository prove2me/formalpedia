-- Prove2me | Theorems.Thm_GlobalTheory_SepCharpoly_charpoly_dvd_of_aeval_eq_zero
-- name    : GlobalTheory.SepCharpoly.charpoly_dvd_of_aeval_eq_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:53:09.455505+00:00
-- url     : https://prove2.me/theorems/84effd43-57c4-421a-93df-2a3a7561a89b
-- title:
--   Sep Charpoly: charpoly dvd of aeval eq zero
-- statement:
--   The Sep Charpoly construction uses the charpoly dvd of aeval eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CharpolyDvdOfAevalEqZero.lean#L11-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CharpolyDvdOfAevalEqZero.lean#L11-L26

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CharpolyDvdOfAevalEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix Formalism.UG
open GlobalTheory GlobalTheory.SepCharpoly

theorem GlobalTheory.SepCharpoly.charpoly_dvd_of_aeval_eq_zero :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (M : Matrix (Fin n) (Fin n) R) (p : R[X]),
      M.charpoly.Separable → aeval M p = 0 → M.charpoly ∣ p := by sorry
