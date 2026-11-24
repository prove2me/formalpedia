-- Prove2me | Theorems.Thm_GlobalTheory_BoundedGL_isCompact_le
-- name    : GlobalTheory.BoundedGL.isCompact_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:01:30.959812+00:00
-- url     : https://prove2.me/theorems/9b8c66f7-6322-4c36-9be4-4e0f2d2eb714
-- title:
--   Bounded GL: is Compact le
-- statement:
--   The Bounded GL construction uses the is Compact le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsCompactGLBoundedEntriesCompletionFinitePlace.lean#L12-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsCompactGLBoundedEntriesCompletionFinitePlace.lean#L12-L47

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicIntegersCompact_IsCompactAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCompactGLBoundedEntriesCompletionFinitePlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
noncomputable section
open GlobalTheory GlobalTheory.BoundedGL
variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

theorem GlobalTheory.BoundedGL.isCompact_le (c : WithZero (Multiplicative ℤ)) :
    IsCompact {x : w.adicCompletion E | Valued.v x ≤ c} := by sorry
