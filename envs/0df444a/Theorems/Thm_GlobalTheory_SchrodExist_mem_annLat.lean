-- Prove2me | Theorems.Thm_GlobalTheory_SchrodExist_mem_annLat
-- name    : GlobalTheory.SchrodExist.mem_annLat
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:48:06.331176+00:00
-- url     : https://prove2.me/theorems/3b44ecc0-9d3c-4265-9932-eaca5a865dd4
-- title:
--   Schrod Exist: mem ann Lat
-- statement:
--   The Schrod Exist construction uses the mem ann Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsSchrodingerIntertwinerIntegralMatrices.lean#L130-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsSchrodingerIntertwinerIntegralMatrices.lean#L130-L132

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LinearIndependentWave
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegersModNatFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsNeZeroOfEventually
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsSchrodingerIntertwinerIntegralMatrices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel GlobalTheory.SplitWeil Matrix
noncomputable section
open GlobalTheory GlobalTheory.SchrodExist
open GlobalTheory.PlaceModel

theorem GlobalTheory.SchrodExist.mem_annLat {k : Type} [Field k] [ValuativeRel k] {Y Y' Z : Type} [AddCommGroup Z]
    {χ : Matrix Y Y' k → Z → ℂ} {hr : ∀ a z z', χ a (z + z') = χ a z * χ a z'} {h0 : ∀ a, χ a 0 = 1} {z : Z} :
    z ∈ annLat χ hr h0 ↔ ∀ u : Matrix Y Y' k, (∀ r q, u r q ∈ 𝒪[k]) → χ u z = 1 := by sorry
