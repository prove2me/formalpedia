-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DifferentConjugateDefects_le_defectAt_vw_of_mem
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.le_defectAt_vw_of_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:08:03.590117+00:00
-- url     : https://prove2.me/theorems/4cb002d0-9368-5c51-aee8-c4b7f626c17a
-- title:
--   Different Conjugate Defects: le defect At vw of mem
-- statement:
--   The Different Conjugate Defects construction uses the le defect At vw of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/SchurLatticeConjugates.lean#L75-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/SchurLatticeConjugates.lean#L75-L80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_SchurLatticeConjugates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

theorem GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.le_defectAt_vw_of_mem {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (σ : E →+* K) (n' : ℕ+) (a : ℕ) (la : HeightOneSpectrum (𝓞 K))
    (h : ((n' : ℕ) : 𝓞 K) ∈ la.asIdeal) : a ≤ defectAt_vw σ n' a la := by sorry
