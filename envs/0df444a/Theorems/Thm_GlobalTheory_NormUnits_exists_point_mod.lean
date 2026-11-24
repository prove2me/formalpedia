-- Prove2me | Theorems.Thm_GlobalTheory_NormUnits_exists_point_mod
-- name    : GlobalTheory.NormUnits.exists_point_mod
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:35:59.331801+00:00
-- url     : https://prove2.me/theorems/015c87a8-430e-4eec-9b95-8e0859657a4f
-- title:
--   Norm Units: exists point mod
-- statement:
--   The Norm Units construction uses the exists point mod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TotalDegreeCMulXMulX.lean#L75-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TotalDegreeCMulXMulX.lean#L75-L127

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
open MvPolynomial
variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]

theorem GlobalTheory.NormUnits.exists_point_mod [LocallyCompactSpace K] (s t c : K) (hs : ‖s‖ ≤ 1) (ht : ‖t‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    ∃ a b z : K, ‖a‖ ≤ 1 ∧ ‖b‖ ≤ 1 ∧ ‖z‖ ≤ 1 ∧ (‖a‖ = 1 ∨ ‖b‖ = 1 ∨ ‖z‖ = 1) ∧
      ‖a ^ 2 + s * a * b + t * b ^ 2 - c * z ^ 2‖ < 1 := by sorry
