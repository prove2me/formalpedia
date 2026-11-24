-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_VacLoc_BigCellLocal_Wm_mul_self
-- name    : GlobalTheory.CompanionTheory.VacLoc.BigCellLocal.Wm_mul_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:50.833094+00:00
-- url     : https://prove2.me/theorems/de095e2e-a703-4e36-b314-ccc6f46b3ad3
-- title:
--   Big Cell Local: Wm mul self
-- statement:
--   The Big Cell Local construction uses the Wm mul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/BigCellLocal.lean#L44-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/BigCellLocal.lean#L44-L45

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

theorem GlobalTheory.CompanionTheory.VacLoc.BigCellLocal.Wm_mul_self : Wm A β * Wm A β = 1 := by sorry
