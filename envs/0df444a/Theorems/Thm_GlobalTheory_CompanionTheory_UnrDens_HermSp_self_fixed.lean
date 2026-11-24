-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_HermSp_self_fixed
-- name    : GlobalTheory.CompanionTheory.UnrDens.HermSp.self_fixed
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:21:02.409298+00:00
-- url     : https://prove2.me/theorems/ac515cee-bd20-45d4-8e3f-639c41e36ced
-- title:
--   Herm Sp: self fixed
-- statement:
--   The Herm Sp construction uses the self fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ResAlgSplitTwo.lean#L86-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ResAlgSplitTwo.lean#L86-L87

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

theorem GlobalTheory.CompanionTheory.UnrDens.HermSp.self_fixed (hτ : ∀ a, τ (τ a) = a) (v : V) : τ (B.h v v) = B.h v v := by sorry
