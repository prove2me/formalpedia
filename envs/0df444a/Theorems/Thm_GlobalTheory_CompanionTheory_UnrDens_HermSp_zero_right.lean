-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_HermSp_zero_right
-- name    : GlobalTheory.CompanionTheory.UnrDens.HermSp.zero_right
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:01:35.222616+00:00
-- url     : https://prove2.me/theorems/0ac5714b-e5b3-4e83-b9c5-76e0a671729a
-- title:
--   Herm Sp: zero right
-- statement:
--   The Herm Sp construction uses the zero right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ResAlgSplitTwo.lean#L77-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ResAlgSplitTwo.lean#L77-L78

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens
variable {E : Type} [CommRing E] {τ : E →+* E}
variable {V : Type} [AddCommGroup V] [Module E V]
open GlobalTheory.CompanionTheory.UnrDens.HermSp
variable (B : HermSp E τ V)

theorem GlobalTheory.CompanionTheory.UnrDens.HermSp.zero_right (v : V) : B.h v 0 = 0 := by sorry
