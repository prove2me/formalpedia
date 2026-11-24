-- Prove2me | Theorems.Thm_GlobalTheory_Idele_mulEquiv_injective
-- name    : GlobalTheory.Idele.mulEquiv_injective
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:52:15.659009+00:00
-- url     : https://prove2.me/theorems/8190eca8-0e66-420c-a301-0bbb4e46ceca
-- title:
--   Idele: mul Equiv injective
-- statement:
--   The Idele construction uses the mul Equiv injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUniqueIdeleOfLinearEquivQuotientLocal.lean#L731-L737
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUniqueIdeleOfLinearEquivQuotientLocal.lean#L731-L737

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

theorem GlobalTheory.Idele.mulEquiv_injective {t s : 𝔸ᶠ[R, K]ˣ} {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0)
    (h : J = t • I) (h' : J = s • I) (e : mulEquiv t hI h = mulEquiv s hI h') : t = s := by sorry
