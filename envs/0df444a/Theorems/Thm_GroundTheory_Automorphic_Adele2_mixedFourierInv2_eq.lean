-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Adele2_mixedFourierInv2_eq
-- name    : GroundTheory.Automorphic.Adele2.mixedFourierInv2_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:49:31.710002+00:00
-- url     : https://prove2.me/theorems/74a6be34-33ad-4c28-9112-14ae25874189
-- title:
--   Adele2: mixed Fourier Inv2 eq
-- statement:
--   The Adele2 construction uses the mixed Fourier Inv2 eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/SummableNormIffAndTsumEqCoset2.lean#L96-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/SummableNormIffAndTsumEqCoset2.lean#L96-L102

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

theorem GroundTheory.Automorphic.Adele2.mixedFourierInv2_eq (f : (Fin 2 → mixedSpace K) → ℂ) (x : Fin 2 → mixedSpace K) :
    mixedFourierInv2 K f x = 𝓕⁻ (f ∘ (toEuclid2Conj K).symm) (toEuclid2 K x) := by sorry
