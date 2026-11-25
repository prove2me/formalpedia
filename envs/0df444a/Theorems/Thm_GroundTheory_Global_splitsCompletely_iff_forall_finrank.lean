-- Prove2me | Theorems.Thm_GroundTheory_Global_splitsCompletely_iff_forall_finrank
-- name    : GroundTheory.Global.splitsCompletely_iff_forall_finrank
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:45:17.975514+00:00
-- url     : https://prove2.me/theorems/bc00610f-42ee-4546-82dc-f8171524669b
-- title:
--   Global: splits Completely iff forall finrank
-- statement:
--   The Global construction uses the splits Completely iff forall finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/Splitting.lean#L62-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/Splitting.lean#L62-L72

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Finite
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Galois
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
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
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField Module
open scoped TensorProduct
open SemiLocal
variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
variable {L} (v : HeightOneSpectrum (𝓞 K))

theorem GroundTheory.Global.splitsCompletely_iff_forall_finrank :
    SplitsCompletely L v ↔
      ∀ w : PlacesOver L v, finrank (v.adicCompletion K) (w.1.adicCompletion L) = 1 := by sorry
