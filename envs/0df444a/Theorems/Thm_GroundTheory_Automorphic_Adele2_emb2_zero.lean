-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Adele2_emb2_zero
-- name    : GroundTheory.Automorphic.Adele2.emb2_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:47:31.013095+00:00
-- url     : https://prove2.me/theorems/6f5cf3af-f9d5-4ae9-afed-a80b510df8e7
-- title:
--   Adele2: emb2 zero
-- statement:
--   The Adele2 construction uses the emb2 zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/SummableNormIffAndTsumEqCoset2.lean#L358-L360
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/SummableNormIffAndTsumEqCoset2.lean#L358-L360

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_SummableNormIffAndTsumEqCoset2
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Adele2
open GroundTheory.Global NumberField NumberField.mixedEmbedding MeasureTheory Module Filter
open scoped FourierTransform SchwartzMap RealInnerProductSpace nonZeroDivisors Classical
set_option synthInstance.maxSize 1000
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
omit [NumberField K]

theorem GroundTheory.Automorphic.Adele2.emb2_zero : emb2 K 0 = 0 := by sorry
