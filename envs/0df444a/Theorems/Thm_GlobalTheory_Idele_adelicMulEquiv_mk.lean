-- Prove2me | Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- name    : GlobalTheory.Idele.adelicMulEquiv_mk
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:51:51.158456+00:00
-- url     : https://prove2.me/theorems/6f47a2e5-b0a5-4434-adb0-fcec7578c325
-- title:
--   Idele: adelic Mul Equiv mk
-- statement:
--   The Idele construction uses the adelic Mul Equiv mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUniqueIdeleOfLinearEquivQuotientLocal.lean#L496-L499
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUniqueIdeleOfLinearEquivQuotientLocal.lean#L496-L499

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

theorem GlobalTheory.Idele.adelicMulEquiv_mk (t : 𝔸ᶠ[R, K]ˣ) {I J : FractionalIdeal R⁰ K} (h : J = t • I)
    (a : 𝔸ᶠ[R, K]) :
    adelicMulEquiv t h (Submodule.Quotient.mk a) = Submodule.Quotient.mk ((t : 𝔸ᶠ[R, K]) * a) := by sorry

attribute [defeq] GlobalTheory.Idele.adelicMulEquiv_mk
