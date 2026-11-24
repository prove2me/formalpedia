-- Prove2me | Theorems.Thm_GlobalTheory_RowLev_Inhab_exists_reduction
-- name    : GlobalTheory.RowLev.Inhab.exists_reduction
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:39:31.28474+00:00
-- url     : https://prove2.me/theorems/31ea8478-299b-4ace-877e-b3a0c6ea8059
-- title:
--   Inhab: exists reduction
-- statement:
--   The Inhab construction uses the exists reduction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/ExistsReduction.lean#L208-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/ExistsReduction.lean#L208-L258

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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem GlobalTheory.RowLev.Inhab.exists_reduction (p : ℕ) (hp : p.Prime) (w : HeightOneSpectrum (𝓞 E)) (hw : Ideal.absNorm w.asIdeal = p) :
    ∃ r : IntAf F E →+* ZMod p, ∀ a, r (psi F E a) = 0 ↔ a ∈ w.asIdeal := by sorry
