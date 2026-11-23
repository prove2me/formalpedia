-- Prove2me | Theorems.Thm_GlobalTheory_BK_coeff_frob
-- name    : GlobalTheory.BK.coeff_frob
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:59.203447+00:00
-- url     : https://prove2.me/theorems/c3ec46a8-fac9-4169-830f-6c8bcdf07174
-- title:
--   BK: coeff frob
-- statement:
--   The BK construction uses the coeff frob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L286-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L286-L287

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
omit [IsUltrametricDist K] [IsUnitBall O K]

theorem GlobalTheory.BK.coeff_frob (l : ℕ) [Fact l.Prime] (f : K⟦X⟧) (n : ℕ) :
    coeff n (frob K l f) = if l ∣ n then coeff (n / l) f else 0 := by sorry
