-- Prove2me | Theorems.Thm_GlobalTheory_Lin_PsiToPi_intInt_inv_log
-- name    : GlobalTheory.Lin.PsiToPi.intInt_inv_log
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:39:43.728578+00:00
-- url     : https://prove2.me/theorems/1896ba7c-479e-42cb-9cfd-fe3bb2838fde
-- title:
--   Psi To Pi: int Int inv log
-- statement:
--   The Psi To Pi construction uses the int Int inv log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PrimeCountRelativeErrorOfPsiRelativeError.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PrimeCountRelativeErrorOfPsiRelativeError.lean#L20-L25

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

theorem GlobalTheory.Lin.PsiToPi.intInt_inv_log {x : ℝ} (hx : 1 < x) : IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume 2 x := by sorry
