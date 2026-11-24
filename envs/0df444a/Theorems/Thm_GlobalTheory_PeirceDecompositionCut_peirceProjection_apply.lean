-- Prove2me | Theorems.Thm_GlobalTheory_PeirceDecompositionCut_peirceProjection_apply
-- name    : GlobalTheory.PeirceDecompositionCut.peirceProjection_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:50.790996+00:00
-- url     : https://prove2.me/theorems/0e0c0382-fbb8-4561-94ca-d1d080be8802
-- title:
--   Peirce Decomposition Cut: peirce Projection apply
-- statement:
--   The Peirce Decomposition Cut construction uses the peirce Projection apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/OneSubSmulPeirceCut.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/OneSubSmulPeirceCut.lean#L20-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_OneSubSmulPeirceCut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PeirceDecompositionCut
variable {R : Type*} [CommRing R] (A : Type*) [Ring A] [Algebra R A]
variable {A}

theorem GlobalTheory.PeirceDecompositionCut.peirceProjection_apply (e : R) (he : IsIdempotentElem e) (x : A) :
    peirceCut A e he x = e • x + (1 - e) • (1 : A) := by sorry

attribute [defeq] GlobalTheory.PeirceDecompositionCut.peirceProjection_apply
