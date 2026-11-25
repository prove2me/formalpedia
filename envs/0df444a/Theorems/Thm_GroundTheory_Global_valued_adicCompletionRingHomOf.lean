-- Prove2me | Theorems.Thm_GroundTheory_Global_valued_adicCompletionRingHomOf
-- name    : GroundTheory.Global.valued_adicCompletionRingHomOf
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:53:24.299087+00:00
-- url     : https://prove2.me/theorems/71698bf4-cc7d-4caf-8661-073091981018
-- title:
--   Global: valued adic Completion Ring Hom Of
-- statement:
--   The Global construction uses the valued adic Completion Ring Hom Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CompletionAtPlace/Galois.lean#L113-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CompletionAtPlace/Galois.lean#L113-L127

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Degree
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Galois
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
open scoped WithZero Pointwise
open GroundTheory GroundTheory.Global
variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L]
  (w : HeightOneSpectrum (𝓞 L))
variable {w}

theorem GroundTheory.Global.valued_adicCompletionRingHomOf (σ : L ≃ₐ[K] L) (hσ : σ • w.asIdeal = w.asIdeal)
    (y : w.adicCompletion L) : Valued.v (adicCompletionRingHomOf w σ hσ y) = Valued.v y := by sorry
