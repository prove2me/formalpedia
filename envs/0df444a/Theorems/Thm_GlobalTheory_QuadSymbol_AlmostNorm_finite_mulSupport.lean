-- Prove2me | Theorems.Thm_GlobalTheory_QuadSymbol_AlmostNorm_finite_mulSupport
-- name    : GlobalTheory.QuadSymbol.AlmostNorm.finite_mulSupport
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:09:26.007441+00:00
-- url     : https://prove2.me/theorems/44d8e724-95d1-4574-9b62-25c1ce3cf6d6
-- title:
--   Almost Norm: finite mul Support
-- statement:
--   The Almost Norm construction uses the finite mul Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/QuadraticClassFieldTheory.lean#L199-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/QuadraticClassFieldTheory.lean#L199-L206

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open GlobalTheory GlobalTheory.QuadSymbol
variable (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
open NumberField IsDedekindDomain
open scoped TensorProduct
variable (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]

theorem GlobalTheory.QuadSymbol.AlmostNorm.finite_mulSupport
    {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L]
    {x : _root_.GlobalTheory.QuadSymbol.FinFam K} (h : _root_.GlobalTheory.QuadSymbol.AlmostNorm K L x) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) =>
      _root_.GlobalTheory.QuadSymbol.eta K L (v.adicCompletion K) (x v)).Finite := by sorry
