-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_GradedSeries_serMul_finite
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.serMul_finite
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:04:11.72041+00:00
-- url     : https://prove2.me/theorems/522bf0f9-d8da-4e94-96b4-d78da30b0c79
-- title:
--   Graded Series: ser Mul finite
-- statement:
--   The Graded Series construction uses the ser Mul finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/GradedSeries.lean#L22-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/GradedSeries.lean#L22-L32

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_GradedSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct
variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]
open TensorProduct
variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]

theorem GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.serMul_finite (f : PowerSeries L) {u : ℤ → M}
    (hu : _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.IsLaurent u) (k : ℤ) :
    (Function.support fun j : ℕ => PowerSeries.coeff j f • u (k - (j : ℤ))).Finite := by sorry
