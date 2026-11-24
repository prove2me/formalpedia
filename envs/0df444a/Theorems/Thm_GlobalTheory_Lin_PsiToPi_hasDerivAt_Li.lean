-- Prove2me | Theorems.Thm_GlobalTheory_Lin_PsiToPi_hasDerivAt_Li
-- name    : GlobalTheory.Lin.PsiToPi.hasDerivAt_Li
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:05:59.388928+00:00
-- url     : https://prove2.me/theorems/eaad7682-1fb1-4307-bbfb-5b4af5bf03d7
-- title:
--   Psi To Pi: has Deriv At Li
-- statement:
--   The Psi To Pi construction uses the has Deriv At Li property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PrimeCountRelativeErrorOfPsiRelativeError.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PrimeCountRelativeErrorOfPsiRelativeError.lean#L27-L30

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

theorem GlobalTheory.Lin.PsiToPi.hasDerivAt_Li {x : ℝ} (hx : 1 < x) : HasDerivAt Li (1 / Real.log x) x := by sorry
