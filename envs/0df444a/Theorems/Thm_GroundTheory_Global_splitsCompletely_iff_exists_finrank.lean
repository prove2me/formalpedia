-- Prove2me | Theorems.Thm_GroundTheory_Global_splitsCompletely_iff_exists_finrank
-- name    : GroundTheory.Global.splitsCompletely_iff_exists_finrank
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:56:30.286406+00:00
-- url     : https://prove2.me/theorems/e0ad58e7-47b7-5e04-a29d-3c6f0995bf45
-- title:
--   Global: splits Completely iff exists finrank
-- statement:
--   The Global construction uses the splits Completely iff exists finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/Splitting.lean#L95-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/Splitting.lean#L95-L101

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

theorem GroundTheory.Global.splitsCompletely_iff_exists_finrank [IsGalois K L] :
    SplitsCompletely L v ↔
      ∃ w : PlacesOver L v, finrank (v.adicCompletion K) (w.1.adicCompletion L) = 1 := by sorry
