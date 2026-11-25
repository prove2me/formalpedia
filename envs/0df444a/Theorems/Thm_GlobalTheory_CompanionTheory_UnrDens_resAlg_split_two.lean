-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_resAlg_split_two
-- name    : GlobalTheory.CompanionTheory.UnrDens.resAlg_split_two
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:01:42.696255+00:00
-- url     : https://prove2.me/theorems/1052d817-cc5d-468b-8c6b-e7e3118260e6
-- title:
--   Unr Dens: res Alg split two
-- statement:
--   The Unr Dens construction uses the res Alg split two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ResAlgSplitTwo.lean#L28-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ResAlgSplitTwo.lean#L28-L56

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

theorem GlobalTheory.CompanionTheory.UnrDens.resAlg_split_two :
    ResAlg (ZMod 2 × ZMod 2) (RingEquiv.prodComm : ZMod 2 × ZMod 2 ≃+* ZMod 2 × ZMod 2).toRingHom 2 1 := by sorry
