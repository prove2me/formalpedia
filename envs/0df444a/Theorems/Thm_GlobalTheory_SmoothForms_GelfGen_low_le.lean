-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_GelfGen_low_le
-- name    : GlobalTheory.SmoothForms.GelfGen.low_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:29:40.313748+00:00
-- url     : https://prove2.me/theorems/c9dd73de-37ad-4cfa-8e69-20a8b32e38a5
-- title:
--   Gelf Gen: low le
-- statement:
--   The Gelf Gen construction uses the low le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/GelfAMemAdjoinLow.lean#L174-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/GelfAMemAdjoinLow.lean#L174-L176

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

theorem GlobalTheory.SmoothForms.GelfGen.low_le (E : Fin n → Fin n → A) :
    Algebra.adjoin ℂ (Set.range fun k : Fin n => gelfA E k.val) ≤ Algebra.adjoin ℂ (Set.range (gelfA E)) := by sorry
