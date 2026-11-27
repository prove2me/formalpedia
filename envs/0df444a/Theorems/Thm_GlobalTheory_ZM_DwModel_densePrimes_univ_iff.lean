-- Prove2me | Theorems.Thm_GlobalTheory_ZM_DwModel_densePrimes_univ_iff
-- name    : GlobalTheory.ZM.DwModel.densePrimes_univ_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:44:08.717525+00:00
-- url     : https://prove2.me/theorems/6023ebfa-fd82-51c1-8c3c-2be1d62108fb
-- title:
--   Dw Model: dense Primes univ iff
-- statement:
--   The Dw Model construction uses the dense Primes univ iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ModuliSpaces/NotIsGaloisCoverTrivial.lean#L100-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ModuliSpaces/NotIsGaloisCoverTrivial.lean#L100-L110

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_NotIsGaloisCoverTrivial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.DwModel

theorem GlobalTheory.ZM.DwModel.densePrimes_univ_iff (R : Type) [CommRing R] : DenseP (Set.univ : Set (Ideal R)) ↔ _root_.IsReduced R := by sorry
