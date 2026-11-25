-- Prove2me | Theorems.Thm_GlobalTheory_RowLev_Inhab_rank_eq_of_std
-- name    : GlobalTheory.RowLev.Inhab.rank_eq_of_std
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:28:13.417258+00:00
-- url     : https://prove2.me/theorems/6c435d60-f0b3-5b6f-9f91-f714e51ef068
-- title:
--   Inhab: rank eq of std
-- statement:
--   The Inhab construction uses the rank eq of std property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/ExistsReduction.lean#L485-L487
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/ExistsReduction.lean#L485-L487

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
open GlobalTheory.RowLev.Inhab

theorem GlobalTheory.RowLev.Inhab.rank_eq_of_std {I : AutInst} (hI : ∀ y, y ∈ I.Lf ↔ ∀ i, y i ∈ IntAf I.F I.E) {N p : ℕ}
    {w : HeightOneSpectrum (𝓞 I.E)} (fr : PlFrame I N p w) : N = I.n := by sorry
