-- Prove2me | Theorems.Thm_GlobalTheory_PrinProd_isSubquotient_prinSeries_multiProd
-- name    : GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:01:57.020807+00:00
-- url     : https://prove2.me/theorems/88c23f70-1c51-4904-87c7-efe96a650eac
-- title:
--   Prin Prod: is Subquotient prin Series multi Prod
-- statement:
--   The Prin Prod construction uses the is Subquotient prin Series multi Prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/PrincipalSeriesSubquotientOfCharacters.lean#L13-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/PrincipalSeriesSubquotientOfCharacters.lean#L13-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviEmbMulSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsIrreducibleIffOfLinearEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PrincipalSeriesSubquotientOfCharacters
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp GlobalTheory.IndefiniteRowSideFullHecke.TameConstituentPlaces ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)
open scoped TensorProduct
open GlobalTheory GlobalTheory.PrinProd

theorem GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (χ : Fin N → kˣ →* ℂˣ) :
    IsSubquotient (prinSeries χ)
      (multiProd (Equiv.sigmaUnique (Fin N) fun _ => Fin 1) fun i => detRep (Fin 1) (χ i)) := by sorry
