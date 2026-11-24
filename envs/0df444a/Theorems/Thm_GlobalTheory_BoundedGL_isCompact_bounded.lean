-- Prove2me | Theorems.Thm_GlobalTheory_BoundedGL_isCompact_bounded
-- name    : GlobalTheory.BoundedGL.isCompact_bounded
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:02:12.567631+00:00
-- url     : https://prove2.me/theorems/60d06a95-0c84-4e63-bb1a-4425a55694ad
-- title:
--   Bounded GL: is Compact bounded
-- statement:
--   The Bounded GL construction uses the is Compact bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsCompactGLBoundedEntriesCompletionFinitePlace.lean#L49-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsCompactGLBoundedEntriesCompletionFinitePlace.lean#L49-L68

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

theorem GlobalTheory.BoundedGL.isCompact_bounded : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (c : WithZero (Multiplicative ℤ)), IsCompact {g : GL (Fin n) (w.adicCompletion E) | ∀ i j,
      Valued.v ((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c ∧
      Valued.v (((g⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c} := by sorry
