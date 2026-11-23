-- Prove2me | Theorems.Thm_GlobalTheory_Lin_PsiToPi_contOn_inv_log
-- name    : GlobalTheory.Lin.PsiToPi.contOn_inv_log
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:39:27.305997+00:00
-- url     : https://prove2.me/theorems/62a6df76-ce84-4870-bafc-3a588f11f419
-- title:
--   Psi To Pi: cont On inv log
-- statement:
--   The Psi To Pi construction uses the cont On inv log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PrimeCountRelativeErrorOfPsiRelativeError.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PrimeCountRelativeErrorOfPsiRelativeError.lean#L16-L18

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

theorem GlobalTheory.Lin.PsiToPi.contOn_inv_log : ContinuousOn (fun t : ℝ => 1 / Real.log t) (Set.Ioi 1) := by sorry
