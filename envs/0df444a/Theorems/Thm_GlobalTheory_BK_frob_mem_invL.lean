-- Prove2me | Theorems.Thm_GlobalTheory_BK_frob_mem_invL
-- name    : GlobalTheory.BK.frob_mem_invL
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:57:05.459871+00:00
-- url     : https://prove2.me/theorems/fe806cdd-e14e-4682-a044-cd978b6b73d9
-- title:
--   BK: frob mem inv L
-- statement:
--   The BK construction uses the frob mem inv L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L457-L460
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L457-L460

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

theorem GlobalTheory.BK.frob_mem_invL (l : ℕ) [Fact l.Prime] {B : Subalgebra O K⟦X⟧}
    (hB : ∀ f ∈ B, frob K l f ∈ B) {f : K⟦X⟧} (hf : f ∈ invL l B) : frob K l f ∈ invL l B := by sorry
