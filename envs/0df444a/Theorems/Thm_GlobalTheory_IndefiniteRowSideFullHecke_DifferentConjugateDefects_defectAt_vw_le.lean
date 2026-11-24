-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DifferentConjugateDefects_defectAt_vw_le
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.defectAt_vw_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:14:59.268832+00:00
-- url     : https://prove2.me/theorems/aca027da-8f4b-48d1-a017-c4120eff243a
-- title:
--   Different Conjugate Defects: defect At vw le
-- statement:
--   The Different Conjugate Defects construction uses the defect At vw le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/SchurLatticeConjugates.lean#L70-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/SchurLatticeConjugates.lean#L70-L73

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.defectAt_vw_le {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (σ : E →+* K) (n' : ℕ+) (a : ℕ) (la : HeightOneSpectrum (𝓞 K)) :
    defectAt_vw σ n' a la ≤ defect_vw E n' a la := by sorry
