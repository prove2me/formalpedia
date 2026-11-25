-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_disc_prod
-- name    : GroundTheory.Automorphic.HermitianForm.disc_prod
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:16:08.536354+00:00
-- url     : https://prove2.me/theorems/2e2819f2-6317-4ca8-828c-95c39ada99ac
-- title:
--   Hermitian Form: disc prod
-- statement:
--   The Hermitian Form construction uses the disc prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianDisc.lean#L94-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianDisc.lean#L94-L112

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

theorem GroundTheory.Automorphic.HermitianForm.disc_prod [FiniteDimensional E V] [FiniteDimensional E V'] (h : HermitianForm F E V)
    (h' : HermitianForm F E V') : (h.prod h').disc = h.disc * h'.disc := by sorry
