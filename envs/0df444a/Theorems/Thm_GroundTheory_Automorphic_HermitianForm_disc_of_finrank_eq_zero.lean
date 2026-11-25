-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_disc_of_finrank_eq_zero
-- name    : GroundTheory.Automorphic.HermitianForm.disc_of_finrank_eq_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:14:08.965055+00:00
-- url     : https://prove2.me/theorems/efe08c3b-808e-46b8-8c75-fd2f622627ff
-- title:
--   Hermitian Form: disc of finrank eq zero
-- statement:
--   The Hermitian Form construction uses the disc of finrank eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianDisc.lean#L122-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianDisc.lean#L122-L129

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

theorem GroundTheory.Automorphic.HermitianForm.disc_of_finrank_eq_zero [FiniteDimensional E V] (h : HermitianForm F E V)
    (hV : finrank E V = 0) : h.disc = 1 := by sorry
