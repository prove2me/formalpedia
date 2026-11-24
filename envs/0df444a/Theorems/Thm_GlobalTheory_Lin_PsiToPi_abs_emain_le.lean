-- Prove2me | Theorems.Thm_GlobalTheory_Lin_PsiToPi_abs_emain_le
-- name    : GlobalTheory.Lin.PsiToPi.abs_emain_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:06:17.881004+00:00
-- url     : https://prove2.me/theorems/0017855a-cf37-417a-b18c-29c929535b94
-- title:
--   Psi To Pi: abs emain le
-- statement:
--   The Psi To Pi construction uses the abs emain le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PrimeCountRelativeErrorOfPsiRelativeError.lean#L193-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PrimeCountRelativeErrorOfPsiRelativeError.lean#L193-L206

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PrimeCountRelativeErrorOfPsiRelativeError
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.Lin GlobalTheory.Lin.PsiToPi
open Formalism.HermitianLattices.GL2PrimeSums (Li Emain)

theorem GlobalTheory.Lin.PsiToPi.abs_emain_le {θ : ℤ} {β u : ℝ} (hθ : θ = 0 ∨ θ = 1 ∨ θ = -1) (hβ : 7 / 8 ≤ β) (hβ1 : β ≤ 1)
    (hu : 4 ≤ u) : |Emain θ β u| ≤ 3 * u := by sorry
