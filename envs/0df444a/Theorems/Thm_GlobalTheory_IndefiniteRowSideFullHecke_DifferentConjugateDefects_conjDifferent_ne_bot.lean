-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DifferentConjugateDefects_conjDifferent_ne_bot
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.conjDifferent_ne_bot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:41.042414+00:00
-- url     : https://prove2.me/theorems/e835dd26-7092-4071-a44e-b444f76b34b6
-- title:
--   Different Conjugate Defects: conj Different ne bot
-- statement:
--   The Different Conjugate Defects construction uses the conj Different ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/SchurLatticeConjugates.lean#L15-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/SchurLatticeConjugates.lean#L15-L24

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.conjDifferent_ne_bot {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (σ : E →+* K) : conjDifferent σ ≠ ⊥ := by sorry
