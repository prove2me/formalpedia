-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_diagForm_apply
-- name    : GroundTheory.Automorphic.diagForm_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:53:43.924248+00:00
-- url     : https://prove2.me/theorems/f2294764-0f85-543a-898b-fbd9ea1c085d
-- title:
--   Automorphic: diag Form apply
-- statement:
--   The Automorphic construction uses the diag Form apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianDisc.lean#L177-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianDisc.lean#L177-L178

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianWitt
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianDisc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module Matrix GroundTheory.LocalField
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V V' : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']

theorem GroundTheory.Automorphic.diagForm_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → Fˣ) (x y : ι → E) :
    (diagForm (E := E) a).toSesq x y = ∑ i, conj F E (x i) * algebraMap F E (a i) * y i := by sorry
