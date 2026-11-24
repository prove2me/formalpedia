-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_HermSp_norm_perp
-- name    : GlobalTheory.CompanionTheory.UnrDens.HermSp.norm_perp
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:19:57.518248+00:00
-- url     : https://prove2.me/theorems/b6a19d59-e2d0-4a1a-87bc-0849072ac7b1
-- title:
--   Herm Sp: norm perp
-- statement:
--   The Herm Sp construction uses the norm perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ResAlgSplitTwo.lean#L160-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ResAlgSplitTwo.lean#L160-L164

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

theorem GlobalTheory.CompanionTheory.UnrDens.HermSp.norm_perp {w v : V} (hv : B.h v w = 0) (a : E) :
    B.h (a • w + v) (a • w + v) = a * τ a * B.h w w + B.h v v := by sorry
