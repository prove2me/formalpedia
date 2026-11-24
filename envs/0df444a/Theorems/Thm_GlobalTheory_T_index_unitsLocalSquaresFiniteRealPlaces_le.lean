-- Prove2me | Theorems.Thm_GlobalTheory_T_index_unitsLocalSquaresFiniteRealPlaces_le
-- name    : GlobalTheory.T.index_unitsLocalSquaresFiniteRealPlaces_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:46:36.367584+00:00
-- url     : https://prove2.me/theorems/a0f96930-93a1-4902-a37b-ffaf89ab1322
-- title:
--   T: index units Local Squares Finite Real Places le
-- statement:
--   The T construction uses the index units Local Squares Finite Real Places le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IndexUnitsLocalSquaresFiniteRealPlacesLeStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IndexUnitsLocalSquaresFiniteRealPlacesLeStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexUnitsLocalSquaresFiniteRealPlacesLe
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexUnitsLocalSquaresFiniteRealPlacesLeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.index_unitsLocalSquaresFiniteRealPlaces_le : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))), (locSq F S).index ≠ 0 ∧ (locSq F S).index ≤ 4 ^ (S.card + Fintype.card (InfinitePlace F)) := by sorry
