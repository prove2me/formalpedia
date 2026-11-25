-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_disc_ofUnit
-- name    : GroundTheory.Automorphic.HermitianForm.disc_ofUnit
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:15:05.620404+00:00
-- url     : https://prove2.me/theorems/1c44c3ee-01ce-4229-8efe-8e35fa7f6d49
-- title:
--   Hermitian Form: disc of Unit
-- statement:
--   The Hermitian Form construction uses the disc of Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianDisc.lean#L114-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianDisc.lean#L114-L120

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
open GroundTheory.Automorphic.HermitianForm
variable [Algebra.IsSeparable F E]

theorem GroundTheory.Automorphic.HermitianForm.disc_ofUnit (a : Fˣ) : (ofUnit (E := E) a).disc = QuotientGroup.mk a := by sorry
