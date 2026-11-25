-- Prove2me | Theorems.Thm_GlobalTheory_Idele_smul_le_smul
-- name    : GlobalTheory.Idele.smul_le_smul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:08:08.698809+00:00
-- url     : https://prove2.me/theorems/ae2b14ba-44a2-5e3c-9b75-54c6549959f7
-- title:
--   Idele: smul le smul
-- statement:
--   The Idele construction uses the smul le smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUniqueIdeleOfLinearEquivQuotientLocal.lean#L252-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUniqueIdeleOfLinearEquivQuotientLocal.lean#L252-L254

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationAlgebraMapEqCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped nonZeroDivisors IsDedekindDomain.FiniteAdeleRing
noncomputable section
open GlobalTheory GlobalTheory.Idele
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem GlobalTheory.Idele.smul_le_smul (t : 𝔸ᶠ[R, K]ˣ) {I J : FractionalIdeal R⁰ K} (h : I ≤ J) :
    t • I ≤ t • J := by sorry
