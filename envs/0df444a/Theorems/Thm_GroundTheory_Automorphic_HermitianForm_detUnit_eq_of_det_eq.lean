-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_detUnit_eq_of_det_eq
-- name    : GroundTheory.Automorphic.HermitianForm.detUnit_eq_of_det_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:15:53.576302+00:00
-- url     : https://prove2.me/theorems/f6d35e2c-a4b7-486b-89aa-806ad3eb65d6
-- title:
--   Hermitian Form: det Unit eq of det eq
-- statement:
--   The Hermitian Form construction uses the det Unit eq of det eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianDisc.lean#L45-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianDisc.lean#L45-L51

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

theorem GroundTheory.Automorphic.HermitianForm.detUnit_eq_of_det_eq (h : HermitianForm F E V) (h' : HermitianForm F E V')
    {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (b : Basis ι E V) (b' : Basis ι' E V')
    (hb : (gram h.toSesq b).det = (gram h'.toSesq b').det) : h.detUnit b = h'.detUnit b' := by sorry
