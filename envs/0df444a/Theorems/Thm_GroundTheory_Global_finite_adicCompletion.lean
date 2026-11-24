-- Prove2me | Theorems.Thm_GroundTheory_Global_finite_adicCompletion
-- name    : GroundTheory.Global.finite_adicCompletion
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:41:30.835634+00:00
-- url     : https://prove2.me/theorems/ec32d79c-1673-42e0-9bac-dbd6ed5b9fe5
-- title:
--   Global: finite adic Completion
-- statement:
--   The Global construction uses the finite adic Completion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CompletionAtPlace.lean#L120-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CompletionAtPlace.lean#L120-L121

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero
open GroundTheory GroundTheory.Global
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]

theorem GroundTheory.Global.finite_adicCompletion : Module.Finite (v.adicCompletion K) (w.adicCompletion L) := by sorry
