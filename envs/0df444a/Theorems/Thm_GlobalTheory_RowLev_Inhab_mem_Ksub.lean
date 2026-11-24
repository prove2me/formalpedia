-- Prove2me | Theorems.Thm_GlobalTheory_RowLev_Inhab_mem_Ksub
-- name    : GlobalTheory.RowLev.Inhab.mem_Ksub
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:30:58.335837+00:00
-- url     : https://prove2.me/theorems/6f5f6f17-46ce-41c1-bd70-004a2d4a2606
-- title:
--   Inhab: mem Ksub
-- statement:
--   The Inhab construction uses the mem Ksub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/ExistsReduction.lean#L79-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/ExistsReduction.lean#L79-L79

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
open GlobalTheory.RowLev.Inhab

theorem GlobalTheory.RowLev.Inhab.mem_Ksub (I : AutInst) (x : I.Gf) : x ∈ Ksub I ↔ x ∈ I.Kset := by sorry
