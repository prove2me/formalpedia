-- Prove2me | Theorems.Thm_GlobalTheory_RowLev_PlFrame_ActsAs_mul
-- name    : GlobalTheory.RowLev.PlFrame.ActsAs.mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:30:55.788013+00:00
-- url     : https://prove2.me/theorems/79a060e5-aff4-484c-91a5-1c898288d6ba
-- title:
--   Acts As: mul
-- statement:
--   The Acts As construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/ExistsReduction.lean#L380-L386
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/ExistsReduction.lean#L380-L386

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

theorem GlobalTheory.RowLev.PlFrame.ActsAs.mul {x x' : I.Gf} (hx' : x' ∈ I.Kset) {M M' : Matrix (Fin N) (Fin N) (ZMod p)}
    (h : fr.ActsAs x M) (h' : fr.ActsAs x' M') : fr.ActsAs (x * x') (M * M') := by sorry
