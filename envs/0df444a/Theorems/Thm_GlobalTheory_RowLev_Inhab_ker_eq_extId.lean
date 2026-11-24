-- Prove2me | Theorems.Thm_GlobalTheory_RowLev_Inhab_ker_eq_extId
-- name    : GlobalTheory.RowLev.Inhab.ker_eq_extId
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:38:55.876268+00:00
-- url     : https://prove2.me/theorems/a25049d3-afba-4717-9176-bee672fe4708
-- title:
--   Inhab: ker eq ext Id
-- statement:
--   The Inhab construction uses the ker eq ext Id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/ExistsReduction.lean#L272-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/ExistsReduction.lean#L272-L289

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

theorem GlobalTheory.RowLev.Inhab.ker_eq_extId {I : AutInst} {p : ℕ} (hp : p ≠ 0) {w : HeightOneSpectrum (𝓞 I.E)}
    (r : IntAf I.F I.E →+* ZMod p) (hr : ∀ a, r (psi I.F I.E a) = 0 ↔ a ∈ w.asIdeal) :
    RingHom.ker r = extId I w.asIdeal := by sorry
