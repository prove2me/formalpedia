-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ResKCoords_map_maximalIdeal_of_ringEquiv
-- name    : GlobalTheory.CompanionTheory.ResKCoords.map_maximalIdeal_of_ringEquiv
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:57:50.269977+00:00
-- url     : https://prove2.me/theorems/9a971304-402b-4455-b1c9-43b4a66389fd
-- title:
--   Res KCoords: map maximal Ideal of ring Equiv
-- statement:
--   The Res KCoords construction uses the map maximal Ideal of ring Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/RegularSequenceGermsRegularLocal.lean#L7-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/RegularSequenceGermsRegularLocal.lean#L7-L13

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

theorem GlobalTheory.CompanionTheory.ResKCoords.map_maximalIdeal_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (e : R ≃+* S) :
    Ideal.map e (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S := by sorry
