-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LGroupSection_isClopen_cosetImage
-- name    : GlobalTheory.CompanionTheory.LGroupSection.isClopen_cosetImage
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:52:00.11353+00:00
-- url     : https://prove2.me/theorems/d56126fe-a820-4152-b66f-35374b28c8e7
-- title:
--   LGroup Section: is Clopen coset Image
-- statement:
--   The LGroup Section construction uses the is Clopen coset Image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsContinuousSectionQuotient.lean#L13-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsContinuousSectionQuotient.lean#L13-L31

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsContinuousSectionQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter Set
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LGroupSection
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem GlobalTheory.CompanionTheory.LGroupSection.isClopen_cosetImage (H K : Subgroup G) [IsClosed (H : Set G)]
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) (d : G) :
    IsClopen (cosetImage H K d) := by sorry
