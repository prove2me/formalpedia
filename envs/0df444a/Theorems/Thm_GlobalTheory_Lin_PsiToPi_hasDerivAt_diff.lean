-- Prove2me | Theorems.Thm_GlobalTheory_Lin_PsiToPi_hasDerivAt_diff
-- name    : GlobalTheory.Lin.PsiToPi.hasDerivAt_diff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:05:56.509126+00:00
-- url     : https://prove2.me/theorems/7e16cbc6-5156-4b2a-9258-fd4ab62cbfd1
-- title:
--   Psi To Pi: has Deriv At diff
-- statement:
--   The Psi To Pi construction uses the has Deriv At diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PrimeCountRelativeErrorOfPsiRelativeError.lean#L44-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PrimeCountRelativeErrorOfPsiRelativeError.lean#L44-L57

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

theorem GlobalTheory.Lin.PsiToPi.hasDerivAt_diff (θ : ℤ) {β u : ℝ} (hβ : 0 < β) (hu : 1 < u) :
    HasDerivAt (fun u => Emain θ β u - mainPsi θ β u / Real.log u) (mainPsi θ β u / (u * Real.log u ^ 2)) u := by sorry
