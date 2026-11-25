-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_disc_eq
-- name    : GroundTheory.Automorphic.HermitianForm.disc_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:16:14.139679+00:00
-- url     : https://prove2.me/theorems/6c045e2e-df4d-4f0a-9294-fbd4709bbc1c
-- title:
--   Hermitian Form: disc eq
-- statement:
--   The Hermitian Form construction uses the disc eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianDisc.lean#L68-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianDisc.lean#L68-L80

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

theorem GroundTheory.Automorphic.HermitianForm.disc_eq [FiniteDimensional E V] (h : HermitianForm F E V) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Basis ι E V) : h.disc = QuotientGroup.mk (h.detUnit b) := by sorry
