-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Centraliser_charpoly_dvd_pow_of_aeval_eq_zero
-- name    : GlobalTheory.UnitLemma.Centraliser.charpoly_dvd_pow_of_aeval_eq_zero
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:26:14.444272+00:00
-- url     : https://prove2.me/theorems/70837e3e-b320-49e9-b39d-e9bbf6777236
-- title:
--   Centraliser: charpoly dvd pow of aeval eq zero
-- statement:
--   The Centraliser construction uses the charpoly dvd pow of aeval eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyDvdPowOfAevalEqZero.lean#L9-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyDvdPowOfAevalEqZero.lean#L9-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_UniNilp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyDvdPowOfAevalEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Centraliser

theorem GlobalTheory.UnitLemma.Centraliser.charpoly_dvd_pow_of_aeval_eq_zero {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (p : R[X]) (hp : aeval M p = 0) : M.charpoly ∣ p ^ Fintype.card n := by sorry
