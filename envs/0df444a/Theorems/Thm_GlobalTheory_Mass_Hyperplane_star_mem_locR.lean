-- Prove2me | Theorems.Thm_GlobalTheory_Mass_Hyperplane_star_mem_locR
-- name    : GlobalTheory.Mass.Hyperplane.star_mem_locR
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:10:02.538909+00:00
-- url     : https://prove2.me/theorems/dbf0b122-4d76-5c99-8b1d-3e6d1dcf18a9
-- title:
--   Hyperplane: star mem loc R
-- statement:
--   The Hyperplane construction uses the star mem loc R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/StarMemLocR.lean#L198-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/StarMemLocR.lean#L198-L201

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StarMemLocR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.Hyperplane
variable {K : Type} [Field K] [StarRing K]

theorem GlobalTheory.Mass.Hyperplane.star_mem_locR {P : Ideal (𝓞 K)} (hP : P.IsPrime) {x : K} (hx : x ∈ locR (K := K) P) :
    star x ∈ locR (K := K) P := by sorry
