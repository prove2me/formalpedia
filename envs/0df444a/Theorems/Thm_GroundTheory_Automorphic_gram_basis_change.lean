-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_gram_basis_change
-- name    : GroundTheory.Automorphic.gram_basis_change
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:14:17.259413+00:00
-- url     : https://prove2.me/theorems/900659be-cd90-476b-b8d8-e5505166ba2b
-- title:
--   Automorphic: gram basis change
-- statement:
--   The Automorphic construction uses the gram basis change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianDisc.lean#L14-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianDisc.lean#L14-L21

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

theorem GroundTheory.Automorphic.gram_basis_change {ι : Type*} [Fintype ι] (B : V →ₛₗ[conjHom F E] V →ₗ[E] E)
    (b c : Basis ι E V) :
    gram B c = ((b.toMatrix c).map (conjHom F E))ᵀ * gram B b * b.toMatrix c := by sorry
