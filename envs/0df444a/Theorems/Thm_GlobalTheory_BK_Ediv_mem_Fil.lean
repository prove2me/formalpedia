-- Prove2me | Theorems.Thm_GlobalTheory_BK_Ediv_mem_Fil
-- name    : GlobalTheory.BK.Ediv_mem_Fil
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:55:30.603783+00:00
-- url     : https://prove2.me/theorems/35f2068b-e679-50eb-9199-8084cbf2d6d9
-- title:
--   BK: Ediv mem Fil
-- statement:
--   The BK construction uses the Ediv mem Fil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L627-L629
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L627-L629

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
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
include l

theorem GlobalTheory.BK.Ediv_mem_Fil (e : ℕ) [NeZero e] {j i : ℕ} (h : j ≤ i) :
    (⟨Ediv K l e i, Ediv_mem_S l e i⟩ : S O K e) ∈ Fil O K l e j := by sorry
