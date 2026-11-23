-- Prove2me | Theorems.Thm_GlobalTheory_NormUnits_finite_res
-- name    : GlobalTheory.NormUnits.finite_res
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:53:16.231597+00:00
-- url     : https://prove2.me/theorems/94b3dec3-4288-4228-bc51-cb199462a041
-- title:
--   Norm Units: finite res
-- statement:
--   The Norm Units construction uses the finite res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TotalDegreeCMulXMulX.lean#L47-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TotalDegreeCMulXMulX.lean#L47-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TotalDegreeCMulXMulX
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.NormUnits
variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]

theorem GlobalTheory.NormUnits.finite_res [LocallyCompactSpace K] : Finite (intRing K ⧸ maxIdeal K) := by sorry
