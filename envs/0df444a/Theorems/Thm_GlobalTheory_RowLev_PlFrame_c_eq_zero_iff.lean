-- Prove2me | Theorems.Thm_GlobalTheory_RowLev_PlFrame_c_eq_zero_iff
-- name    : GlobalTheory.RowLev.PlFrame.c_eq_zero_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:39:13.542132+00:00
-- url     : https://prove2.me/theorems/7faff1a7-b06b-4f53-968e-29b4b52840d1
-- title:
--   Pl Frame: c eq zero iff
-- statement:
--   The Pl Frame construction uses the c eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/ExistsReduction.lean#L349-L351
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/ExistsReduction.lean#L349-L351

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

theorem GlobalTheory.RowLev.PlFrame.c_eq_zero_iff (y : I.Lf) :
    fr.c y = 0 ↔ y ∈ extId I w.asIdeal • (⊤ : Submodule (IntAf I.F I.E) I.Lf) := by sorry
