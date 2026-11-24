-- Prove2me | Theorems.Thm_GlobalTheory_Mem_Capelli_adjoin_gelfA
-- name    : GlobalTheory.Mem.Capelli.adjoin_gelfA
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:31:57.660894+00:00
-- url     : https://prove2.me/theorems/cfc22700-b51c-4382-bac5-e693e85cc410
-- title:
--   Capelli: adjoin gelf A
-- statement:
--   The Capelli construction uses the adjoin gelf A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AdjoinGelfandInvariantsDualPairEq.lean#L40-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AdjoinGelfandInvariantsDualPairEq.lean#L40-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AdjoinGelfandInvariantsDualPairEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.Mem.Lift
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Capelli
variable {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ}

theorem GlobalTheory.Mem.Capelli.adjoin_gelfA (E : Fin n → Fin n → A) :
    Algebra.adjoin ℂ (Set.range (GlobalTheory.SmoothForms.gelfA E)) = trAlg (Matrix.of E) := by sorry
