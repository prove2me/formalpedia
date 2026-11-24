-- Prove2me | Theorems.Thm_GlobalTheory_JR_LinDesc_leftMul_tau
-- name    : GlobalTheory.JR.LinDesc.leftMul_tau
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:50:22.420458+00:00
-- url     : https://prove2.me/theorems/5c4b2520-b5b5-4cd0-b941-673e0f0f0f20
-- title:
--   Lin Desc: left Mul tau
-- statement:
--   The Lin Desc construction uses the left Mul tau property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LeftMulTau.lean#L47-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LeftMulTau.lean#L47-L65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.LinDesc
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}

theorem GlobalTheory.JR.LinDesc.leftMul_tau (hG : A.IsGen τ p) : Algebra.leftMulMatrix (LinDesc.bas A hG) τ = companion p := by sorry
