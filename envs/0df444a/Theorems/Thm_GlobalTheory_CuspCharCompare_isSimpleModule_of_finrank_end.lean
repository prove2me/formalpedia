-- Prove2me | Theorems.Thm_GlobalTheory_CuspCharCompare_isSimpleModule_of_finrank_end
-- name    : GlobalTheory.CuspCharCompare.isSimpleModule_of_finrank_end
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:08:43.037591+00:00
-- url     : https://prove2.me/theorems/09067383-988a-44fb-9e53-8ae13a03651a
-- title:
--   Cusp Char Compare: is Simple Module of finrank end
-- statement:
--   The Cusp Char Compare construction uses the is Simple Module of finrank end property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsSimpleModuleOfFinrankEnd.lean#L15-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsSimpleModuleOfFinrankEnd.lean#L15-L44

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_CuspEllipticValues
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_IrreducibleCharacters_CuspidalCharacters
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CentralIdempotentIrreducibleCharacterProps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsSimpleModuleOfFinrankEnd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CuspCharCompare
open CuspElliptic GlobalTheory.IndefiniteRowSideFullHecke.CuspidalCharacters
open scoped MonoidAlgebra
variable {G : Type} [Group G]

theorem GlobalTheory.CuspCharCompare.isSimpleModule_of_finrank_end {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module R M]
    [Module ℂ M] [IsScalarTower ℂ R M] [SMulCommClass R ℂ M] [IsSemisimpleModule R M]
    (h : Module.finrank ℂ (Module.End R M) = 1) : IsSimpleModule R M := by sorry
