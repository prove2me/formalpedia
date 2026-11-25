-- Prove2me | Theorems.Thm_GlobalTheory_IntBall_nmat_eq_lowMat
-- name    : GlobalTheory.IntBall.nmat_eq_lowMat
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:37:09.154419+00:00
-- url     : https://prove2.me/theorems/172be098-7c44-4c54-b364-f68d1a9794a8
-- title:
--   Int Ball: nmat eq low Mat
-- statement:
--   The Int Ball construction uses the nmat eq low Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NmatEqLowMat.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NmatEqLowMat.lean#L35-L38

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_IsStrictDom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntBall
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.IntBall.nmat_eq_lowMat (X : Data E r) (z : V (nd X)) (τ : X.Ψ) :
    (Matrix.of (nmat X z τ) : Matrix (Fin r) (Fin r) ℂ) = lowMat (zOf X z τ) := by sorry
