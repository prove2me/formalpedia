-- Prove2me | Theorems.Thm_GlobalTheory_SchrodExist_inv_nsmul_nsmul
-- name    : GlobalTheory.SchrodExist.inv_nsmul_nsmul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:48:22.708848+00:00
-- url     : https://prove2.me/theorems/fee112ed-cfd4-4ce3-8311-0bd5c5f42b99
-- title:
--   Schrod Exist: inv nsmul nsmul
-- statement:
--   The Schrod Exist construction uses the inv nsmul nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsSchrodingerIntertwinerIntegralMatrices.lean#L134-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsSchrodingerIntertwinerIntegralMatrices.lean#L134-L136

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

theorem GlobalTheory.SchrodExist.inv_nsmul_nsmul {k : Type} [Field k] [CharZero k] {Y Y' : Type} (n : ℕ) (hn : 0 < n)
    (m : Matrix Y Y' k) : (n : k)⁻¹ • (n • m) = m := by sorry
