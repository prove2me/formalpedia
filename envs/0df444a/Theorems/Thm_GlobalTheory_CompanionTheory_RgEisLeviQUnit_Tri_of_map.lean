-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_Tri_of_map
-- name    : GlobalTheory.CompanionTheory.RgEisLeviQUnit.Tri.of_map
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:58:46.74588+00:00
-- url     : https://prove2.me/theorems/d05a107d-b529-4be5-84ac-338d5decbdd2
-- title:
--   Tri: of map
-- statement:
--   The Tri construction uses the of map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviQuotientOfBlockDet.lean#L527-L530
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviQuotientOfBlockDet.lean#L527-L530

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviQuotientOfBlockDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisLeviQUnit
open PositivityTheory.RgEis
variable {R : Type} [CommRing R]

theorem GlobalTheory.CompanionTheory.RgEisLeviQUnit.Tri.of_map {ι : Type} [Fintype ι] [DecidableEq ι] {s : Set ι} {S : Type} [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) {g : Matrix (ι ⊕ ι) (ι ⊕ ι) R} (h : Tri s (g.map f)) : Tri s g := by sorry
