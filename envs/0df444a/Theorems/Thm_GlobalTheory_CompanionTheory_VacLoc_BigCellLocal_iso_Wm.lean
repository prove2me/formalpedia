-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_VacLoc_BigCellLocal_iso_Wm
-- name    : GlobalTheory.CompanionTheory.VacLoc.BigCellLocal.iso_Wm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:10.732841+00:00
-- url     : https://prove2.me/theorems/4708ffce-a1dd-4f7a-b866-f7684fd8fa7b
-- title:
--   Big Cell Local: iso Wm
-- statement:
--   The Big Cell Local construction uses the iso Wm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/BigCellLocal.lean#L54-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/BigCellLocal.lean#L54-L55

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsSkewOfDiagonal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BigCellLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.VacLoc.BigCellLocal
variable {A : Type} [CommRing A] {σ : A →+* A} {β : Type} [Fintype β] [DecidableEq β]

theorem GlobalTheory.CompanionTheory.VacLoc.BigCellLocal.iso_Wm : Iso σ (Wm A β) (Wm A β) (Wm A β) := by sorry
