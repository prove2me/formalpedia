-- Prove2me | Theorems.Thm_GlobalTheory_T_valuation_uniformizer_integralClosure_eq_exp_neg_ramificationIdx
-- name    : GlobalTheory.T.valuation_uniformizer_integralClosure_eq_exp_neg_ramificationIdx
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:40:20.090329+00:00
-- url     : https://prove2.me/theorems/405b5ea4-b69b-575b-a252-f89aff102362
-- title:
--   T: valuation uniformizer integral Closure eq exp neg ramification Idx
-- statement:
--   The T construction uses the valuation uniformizer integral Closure eq exp neg ramification Idx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ValuationUniformizerIntegralClosureEqExpNegRamifStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ValuationUniformizerIntegralClosureEqExpNegRamifStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValuationUniformizerIntegralClosureEqExpNegRamif
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValuationUniformizerIntegralClosureEqExpNegRamifStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.valuation_uniformizer_integralClosure_eq_exp_neg_ramificationIdx : ∀ (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra R L] [IsScalarTower R K L] [IsDedekindDomain (integralClosure R L)] [IsFractionRing (integralClosure R L) L] (P : IsDedekindDomain.HeightOneSpectrum (integralClosure R L)) (π : R), Irreducible π → P.valuation L (algebraMap K L (algebraMap R K π)) = WithZero.exp (-(P.asIdeal.ramificationIdx R : ℤ)) := by sorry
