-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_HermSp_mem_perp
-- name    : GlobalTheory.CompanionTheory.UnrDens.HermSp.mem_perp
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:01:24.221459+00:00
-- url     : https://prove2.me/theorems/49cae741-cbcf-5ba1-9b28-2e7fe47e4592
-- title:
--   Herm Sp: mem perp
-- statement:
--   The Herm Sp construction uses the mem perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ResAlgSplitTwo.lean#L101-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ResAlgSplitTwo.lean#L101-L102

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

theorem GlobalTheory.CompanionTheory.UnrDens.HermSp.mem_perp {w v : V} : v ∈ B.perp w ↔ B.h v w = 0 := by sorry
