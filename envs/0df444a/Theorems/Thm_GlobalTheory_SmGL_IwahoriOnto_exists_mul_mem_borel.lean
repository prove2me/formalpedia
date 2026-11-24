-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_IwahoriOnto_exists_mul_mem_borel
-- name    : GlobalTheory.SmGL.IwahoriOnto.exists_mul_mem_borel
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:13:33.20639+00:00
-- url     : https://prove2.me/theorems/433b94b6-1f7a-4fed-8bd5-680a5503e82e
-- title:
--   Iwahori Onto: exists mul mem borel
-- statement:
--   The Iwahori Onto construction uses the exists mul mem borel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IwahoriProjSurjective.lean#L100-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IwahoriProjSurjective.lean#L100-L140

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel Matrix Topology Filter
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.IwahoriOnto
variable {R n : Type} [CommRing R] [IsLocalRing R] [Fintype n] [DecidableEq n] [LinearOrder n]

theorem GlobalTheory.SmGL.IwahoriOnto.exists_mul_mem_borel (h : GL n R)
    (hh : GeneralLinearGroup.map (IsLocalRing.residue R) h ∈ borel (IsLocalRing.ResidueField R) n) :
    ∃ L : GL n R, (∀ i j, i < j → (L : Matrix n n R) i j = 0) ∧ (∀ i, (L : Matrix n n R) i i = 1) ∧
      h * L ∈ borel R n := by sorry
