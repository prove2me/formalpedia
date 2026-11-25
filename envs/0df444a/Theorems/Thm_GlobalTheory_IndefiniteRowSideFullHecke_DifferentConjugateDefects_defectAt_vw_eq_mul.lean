-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DifferentConjugateDefects_defectAt_vw_eq_mul
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.defectAt_vw_eq_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:08:09.086862+00:00
-- url     : https://prove2.me/theorems/aa027dcd-0848-4272-a94e-9d29ba79c0bd
-- title:
--   Different Conjugate Defects: defect At vw eq mul
-- statement:
--   The Different Conjugate Defects construction uses the defect At vw eq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/SchurLatticeConjugates.lean#L62-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/SchurLatticeConjugates.lean#L62-L68

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.defectAt_vw_eq_mul {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (σ : E →+* K) (n' : ℕ+) (a : ℕ) (la : HeightOneSpectrum (𝓞 K)) (e : ℝ) (he : 0 < e) :
    (defectAt_vw σ n' a la : ℝ) = e * a * max ((ord_vw la (conjDifferent σ) : ℝ) / e)
      ((ord_vw la (Ideal.span {((n' : ℕ) : 𝓞 K)}) : ℝ) / e) := by sorry
