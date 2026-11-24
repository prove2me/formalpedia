-- Prove2me | Theorems.Thm_GroundTheory_Global_KummerIndex_hasEnoughRootsOfUnity_of_ringHom
-- name    : GroundTheory.Global.KummerIndex.hasEnoughRootsOfUnity_of_ringHom
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:40:43.472421+00:00
-- url     : https://prove2.me/theorems/38758f1e-8439-4a44-994d-6adac7871249
-- title:
--   Kummer Index: has Enough Roots Of Unity of ring Hom
-- statement:
--   The Kummer Index construction uses the has Enough Roots Of Unity of ring Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/KummerIndexLemma/HasEnoughRootsOfUnityOfRingHom.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/KummerIndexLemma/HasEnoughRootsOfUnityOfRingHom.lean#L14-L17

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndexAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IndexProductFormula
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerBasic
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_KummerIndexLemma_HasEnoughRootsOfUnityOfRingHom
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
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField GroundTheory.ProfCoh WithZero
open GroundTheory.Global.KummerIndex

theorem GroundTheory.Global.KummerIndex.hasEnoughRootsOfUnity_of_ringHom {F E : Type*} [Field F] [Field E] (f : F →+* E)
    (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity F n] : HasEnoughRootsOfUnity E n := by sorry
