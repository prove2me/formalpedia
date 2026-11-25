-- Prove2me | Theorems.Thm_GlobalTheory_ChowHt_localLength_ne_zero
-- name    : GlobalTheory.ChowHt.localLength_ne_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:10:39.246582+00:00
-- url     : https://prove2.me/theorems/6649ada4-81b9-4fe6-9b0a-5550254b059e
-- title:
--   Chow Ht: local Length ne zero
-- statement:
--   The Chow Ht construction uses the local Length ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/IsMultiHomogeneousFixFirstBlock.lean#L39-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/IsMultiHomogeneousFixFirstBlock.lean#L39-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IrreducibleOfIrreducibleMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallAevalLineVanishingIdealIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ProjPointIdealMemProjComponentsOfIsProjPureDim
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IsMultiHomogeneousFixFirstBlock_b3ed944b577456bc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.ChowHt
variable {R : Type} [CommRing R]

theorem GlobalTheory.ChowHt.localLength_ne_zero {J Q : Ideal R} [Q.IsPrime] (h : J ≤ Q) : localLength J Q ≠ 0 := by sorry
