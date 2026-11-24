-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ResKCoords_rsp_of_ringEquiv
-- name    : GlobalTheory.CompanionTheory.ResKCoords.rsp_of_ringEquiv
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:57:42.469072+00:00
-- url     : https://prove2.me/theorems/ff063a27-d8db-4c2b-abd2-282f37f9f8a2
-- title:
--   Res KCoords: rsp of ring Equiv
-- statement:
--   The Res KCoords construction uses the rsp of ring Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/RegularSequenceGermsRegularLocal.lean#L15-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/RegularSequenceGermsRegularLocal.lean#L15-L22

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_RegularSequenceGermsRegularLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ResKCoords

theorem GlobalTheory.CompanionTheory.ResKCoords.rsp_of_ringEquiv {R S : Type} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (e : R ≃+* S) (m : ℕ) (r : Fin m → R) (h : FinalTheorems.Rsp R m r) :
    FinalTheorems.Rsp S m (fun i => e (r i)) := by sorry
