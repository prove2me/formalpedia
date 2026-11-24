-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_GelfGen_central_of_filt_low
-- name    : GlobalTheory.SmoothForms.GelfGen.central_of_filt_low
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:28:43.6118+00:00
-- url     : https://prove2.me/theorems/2fa2389f-9abe-4e8b-8cd0-827c6c0c13a3
-- title:
--   Gelf Gen: central of filt low
-- statement:
--   The Gelf Gen construction uses the central of filt low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/GelfAMemAdjoinLow.lean#L178-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/GelfAMemAdjoinLow.lean#L178-L228

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
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.GelfGen
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}

theorem GlobalTheory.SmoothForms.GelfGen.central_of_filt_low {E : Fin n → Fin n → A} (hE : Formalism.REAL.GlRel E) (d : ℕ) :
    ∀ z ∈ filt E d, (∀ a b, E a b * z = z * E a b) →
      z ∈ Algebra.adjoin ℂ (Set.range fun k : Fin n => gelfA E k.val) := by sorry
