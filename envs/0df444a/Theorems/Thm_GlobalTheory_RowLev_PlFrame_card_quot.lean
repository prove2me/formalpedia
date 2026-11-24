-- Prove2me | Theorems.Thm_GlobalTheory_RowLev_PlFrame_card_quot
-- name    : GlobalTheory.RowLev.PlFrame.card_quot
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:31:38.104797+00:00
-- url     : https://prove2.me/theorems/b6eae1c9-ee42-41b6-afc6-1ff3a8c00a04
-- title:
--   Pl Frame: card quot
-- statement:
--   The Pl Frame construction uses the card quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/ExistsReduction.lean#L355-L363
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/ExistsReduction.lean#L355-L363

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsApprox
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RowLev
open Formalism.MainNotions.S MeasureTheory NumberField IsDedekindDomain Matrix
open Formalism.UG Formalism.UG.P
open scoped TensorProduct
open Inhab
open GlobalTheory.RowLev.PlFrame
variable {I : AutInst} {N p : ℕ} {w : HeightOneSpectrum (𝓞 I.E)} (fr : PlFrame I N p w)
include fr

theorem GlobalTheory.RowLev.PlFrame.card_quot :
    Nat.card (I.Lf ⧸ (extId I w.asIdeal • (⊤ : Submodule (IntAf I.F I.E) I.Lf))) = p ^ N := by sorry
