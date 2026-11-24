-- Prove2me | Theorems.Thm_GlobalTheory_SchrodExist_mem_intLat
-- name    : GlobalTheory.SchrodExist.mem_intLat
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:48:07.166787+00:00
-- url     : https://prove2.me/theorems/5971da8b-d865-4c11-9fc0-d837dff7d0b2
-- title:
--   Schrod Exist: mem int Lat
-- statement:
--   The Schrod Exist construction uses the mem int Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsSchrodingerIntertwinerIntegralMatrices.lean#L113-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsSchrodingerIntertwinerIntegralMatrices.lean#L113-L114

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

theorem GlobalTheory.SchrodExist.mem_intLat {k : Type} [Field k] [ValuativeRel k] {Y Y' : Type} {x : Matrix Y Y' k} :
    x ∈ intLat k Y Y' ↔ ∀ r q, x r q ∈ 𝒪[k] := by sorry
