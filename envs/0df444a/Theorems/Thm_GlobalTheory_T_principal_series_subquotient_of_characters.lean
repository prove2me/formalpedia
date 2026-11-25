-- Prove2me | Theorems.Thm_GlobalTheory_T_principal_series_subquotient_of_characters
-- name    : GlobalTheory.T.principal_series_subquotient_of_characters
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:36:29.362282+00:00
-- url     : https://prove2.me/theorems/4e85ace3-9d10-5557-aa73-49e4b9226afa
-- title:
--   T: principal series subquotient of characters
-- statement:
--   The T construction uses the principal series subquotient of characters property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/PrincipalSeriesSubquotientOfCharactersStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/PrincipalSeriesSubquotientOfCharactersStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PrincipalSeriesSubquotientOfCharacters
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviEmbMulSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PrincipalSeriesSubquotientOfCharactersStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp GlobalTheory.IndefiniteRowSideFullHecke.TameConstituentPlaces ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.principal_series_subquotient_of_characters : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (χ : Fin N → kˣ →* ℂˣ), IsSubquotient (prinSeries χ) (multiProd (Equiv.sigmaUnique (Fin N) fun _ => Fin 1) fun i => detRep (Fin 1) (χ i)) := by sorry
