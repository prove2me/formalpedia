-- Prove2me | Theorems.Thm_GlobalTheory_SW_LinChange_haarAt_comp
-- name    : GlobalTheory.SW.LinChange.haarAt_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:32.937462+00:00
-- url     : https://prove2.me/theorems/d3ca7216-5088-47a5-aaa0-889ed242d02b
-- title:
--   Lin Change: haar At comp
-- statement:
--   The Lin Change construction uses the haar At comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatInvariantIntegralMatrixMul.lean#L171-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatInvariantIntegralMatrixMul.lean#L171-L198

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.LinChange
variable {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι]

theorem GlobalTheory.SW.LinChange.haarAt_comp (T : Matrix κ ι K ≃ₗ[ℚ] Matrix κ ι K) (R M : ℕ) (hR : 0 < R) (hM : 0 < M)
    (hT : ∀ y, IntM y → IntM ((M : K) • T y)) (φ : Matrix κ ι K → ℂ) (h : HasLevel R φ) :
    haarAt (R * M) (fun x => φ (T x)) =
      ((|LinearMap.det T.toLinearMap| : ℚ) : ℂ) * haarAt R φ := by sorry
