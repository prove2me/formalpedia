-- Prove2me | Theorems.Thm_GroundTheory_Global_finrank_eq_of_isGalois
-- name    : GroundTheory.Global.finrank_eq_of_isGalois
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:14:14.208159+00:00
-- url     : https://prove2.me/theorems/93cb170f-1509-53a8-8ef9-66114456959d
-- title:
--   Global: finrank eq of is Galois
-- statement:
--   The Global construction uses the finrank eq of is Galois property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/Splitting.lean#L89-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/Splitting.lean#L89-L93

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

theorem GroundTheory.Global.finrank_eq_of_isGalois [IsGalois K L] (w w' : PlacesOver L v) :
    finrank (v.adicCompletion K) (w.1.adicCompletion L) =
      finrank (v.adicCompletion K) (w'.1.adicCompletion L) := by sorry
