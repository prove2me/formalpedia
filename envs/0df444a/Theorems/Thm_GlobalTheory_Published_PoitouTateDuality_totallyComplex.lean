-- Prove2me | Theorems.Thm_GlobalTheory_Published_PoitouTateDuality_totallyComplex
-- name    : GlobalTheory.Published.PoitouTateDuality.totallyComplex
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:16:24.089918+00:00
-- url     : https://prove2.me/theorems/05cc2fd4-4cca-543b-b2d8-9b436b521274
-- title:
--   Poitou Tate Duality: totally Complex
-- statement:
--   The Poitou Tate Duality construction uses the totally Complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/ExistsPrimitiveRootPow.lean#L50-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/ExistsPrimitiveRootPow.lean#L50-L56

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__CohDimTwoLocalOfLocalFiniteness_b2c2e165733ad400
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ExistsPrimitiveRootPow_85cddf4c39d1fc1a
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory GlobalTheory.Published
open PoitouTate
open NumberField IsDedekindDomain

theorem GlobalTheory.Published.PoitouTateDuality.totallyComplex (h : _root_.GlobalTheory.Published.PoitouTateDuality) :
    _root_.GlobalTheory.Published.PoitouTateTotallyComplex := by sorry
