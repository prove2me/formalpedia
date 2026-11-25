-- Prove2me | Theorems.Thm_GroundTheory_Global_HeckeCharacter_infiniteComponent_eq
-- name    : GroundTheory.Global.HeckeCharacter.infiniteComponent_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:23:23.984022+00:00
-- url     : https://prove2.me/theorems/9cf2d88a-cc3f-41a6-925b-7dde0413885b
-- title:
--   Hecke Character: infinite Component eq
-- statement:
--   The Hecke Character construction uses the infinite Component eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/EulerFactorsArch.lean#L203-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/EulerFactorsArch.lean#L203-L207

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeChar
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnitary
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_Gaussian
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplex
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_EulerFactorsArch
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField InfinitePlace InfinitePlace.Completion MeasureTheory Complex ComplexConjugate
open scoped Real
open GroundTheory GroundTheory.Global
noncomputable section
open GroundTheory.Global.HeckeCharacter
variable {K : Type*} [Field K] [NumberField K] (χ : HeckeCharacter K)

theorem GroundTheory.Global.HeckeCharacter.infiniteComponent_eq (w : InfinitePlace K) (a : (w.Completion)ˣ) :
    (χ.infiniteComponent w a : ℂ) =
      (extensionEmbedding w (a : w.Completion) / (‖(a : w.Completion)‖ : ℂ)) ^ χ.infiniteWeight w *
        ((‖(a : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ ((χ.infiniteTau w : ℂ) * I) := by sorry
