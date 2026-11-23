-- Prove2me | Theorems.Thm_GlobalTheory_BK_frob_bound
-- name    : GlobalTheory.BK.frob_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:21:02.361466+00:00
-- url     : https://prove2.me/theorems/353550c7-5b2f-43d7-932f-965977d2d769
-- title:
--   BK: frob bound
-- statement:
--   The BK construction uses the frob bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L356-L361
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L356-L361

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NormPowLeNormFactorial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K]
variable {O K}

theorem GlobalTheory.BK.frob_bound (l : ℕ) [Fact l.Prime] {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) (ha : Antitone w)
    (f : K⟦X⟧) (n : ℕ) : ‖coeff n (frob K l f)‖ * w n ≤ ‖coeff (n / l) f‖ * w (n / l) := by sorry
