-- Prove2me | Theorems.Thm_GlobalTheory_BK_smodEq_l_pow_S_iff
-- name    : GlobalTheory.BK.smodEq_l_pow_S_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:34:59.478938+00:00
-- url     : https://prove2.me/theorems/fdd82fc4-5540-406f-9a90-271136f00d41
-- title:
--   BK: smod Eq l pow S iff
-- statement:
--   The BK construction uses the smod Eq l pow S iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MemSpanLPowSIff.lean#L34-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MemSpanLPowSIff.lean#L34-L38

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

theorem GlobalTheory.BK.smodEq_l_pow_S_iff (n : ℕ) (f g : S O K e) :
    f ≡ g [SMOD (Ideal.span {(l : S O K e)} ^ n • ⊤ : Submodule (S O K e) (S O K e))] ↔
      ∀ m, ‖coeff m (f : K⟦X⟧) - coeff m (g : K⟦X⟧)‖ * wS K e m ≤ ‖(l : K)‖ ^ n := by sorry
