-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_gelfA_mem_adjoin_low
-- name    : GlobalTheory.SmoothForms.gelfA_mem_adjoin_low
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:24:28.989706+00:00
-- url     : https://prove2.me/theorems/d73e1110-44ca-4cd7-8b5d-eee955bd494b
-- title:
--   Smooth Forms: gelf A mem adjoin low
-- statement:
--   The Smooth Forms construction uses the gelf A mem adjoin low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/GelfAMemAdjoinLow.lean#L237-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/GelfAMemAdjoinLow.lean#L237-L241

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PermutationWordGelfandPolynomialModShorter
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_PowFinrankEqZeroOfTracePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_GelfAMemAdjoinLow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms
noncomputable section
open GlobalTheory.SmoothForms.PermWord

theorem GlobalTheory.SmoothForms.gelfA_mem_adjoin_low : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A),
    Formalism.REAL.GlRel E → ∀ m : ℕ, gelfA E m ∈ Algebra.adjoin ℂ (Set.range fun k : Fin n => gelfA E k.val) := by sorry
