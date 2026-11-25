-- Prove2me | Theorems.Thm_GlobalTheory_QuadSymbol_exists_almostNorm_etaProd_eq_neg_one
-- name    : GlobalTheory.QuadSymbol.exists_almostNorm_etaProd_eq_neg_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:13:40.528804+00:00
-- url     : https://prove2.me/theorems/76661e12-1fd5-4b60-b4a7-c1c98d8603ae
-- title:
--   Quad Symbol: exists almost Norm eta Prod eq neg one
-- statement:
--   The Quad Symbol construction uses the exists almost Norm eta Prod eq neg one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsAlmostNormEtaProdEqNegOne.lean#L129-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsAlmostNormEtaProdEqNegOne.lean#L129-L162

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsPlaceNotIsSquareAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsLocalNonnormOfNonsquareAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticExtNormFormOverAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsAlmostNormEtaProdEqNegOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.QuadSymbol
open NumberField IsDedekindDomain

theorem GlobalTheory.QuadSymbol.exists_almostNorm_etaProd_eq_neg_one :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      [Algebra.IsQuadraticExtension K L],
      ∃ (x : _root_.GlobalTheory.QuadSymbol.FinFam K) (y : _root_.GlobalTheory.QuadSymbol.InfFam K),
        _root_.GlobalTheory.QuadSymbol.AlmostNorm K L x ∧ _root_.GlobalTheory.QuadSymbol.etaProd K L x y = -1 := by sorry
