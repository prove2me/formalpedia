-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Equi_cosetOff_empty_eq_latCoset
-- name    : GlobalTheory.CompanionTheory.Equi.cosetOff_empty_eq_latCoset
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:38:49.142858+00:00
-- url     : https://prove2.me/theorems/2e3cc098-7898-4814-bda0-bbddeee9c731
-- title:
--   Equi: coset Off empty eq lat Coset
-- statement:
--   The Equi construction uses the coset Off empty eq lat Coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CosetEmptyPlacesLattice.lean#L38-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CosetEmptyPlacesLattice.lean#L38-L47

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetEmptyPlacesLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Equi

theorem GlobalTheory.CompanionTheory.Equi.cosetOff_empty_eq_latCoset (F : Type) [Field F] [NumberField F] (ι : Type)
    (I : Ideal (𝓞 F)) (x0 : ι → F) :
    cosetOff (∅ : Finset (HeightOneSpectrum (𝓞 F))) I x0 = latCoset I x0 := by sorry
