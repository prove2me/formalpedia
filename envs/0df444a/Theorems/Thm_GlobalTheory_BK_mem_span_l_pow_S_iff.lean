-- Prove2me | Theorems.Thm_GlobalTheory_BK_mem_span_l_pow_S_iff
-- name    : GlobalTheory.BK.mem_span_l_pow_S_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:59:20.2355+00:00
-- url     : https://prove2.me/theorems/2386f81b-651a-45f4-b827-6f5f5a1d19f8
-- title:
--   BK: mem span l pow S iff
-- statement:
--   The BK construction uses the mem span l pow S iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MemSpanLPowSIff.lean#L11-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MemSpanLPowSIff.lean#L11-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemSpanLPowSIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BK PowerSeries Filter Topology
open GlobalTheory GlobalTheory.BK
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]

theorem GlobalTheory.BK.mem_span_l_pow_S_iff (n : ℕ) (f : S O K e) :
    f ∈ Ideal.span {(l : S O K e)} ^ n ↔
      ∀ m, ‖coeff m (f : K⟦X⟧)‖ * wS K e m ≤ ‖(l : K)‖ ^ n := by sorry
