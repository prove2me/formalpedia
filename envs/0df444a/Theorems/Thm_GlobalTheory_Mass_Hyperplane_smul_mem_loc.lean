-- Prove2me | Theorems.Thm_GlobalTheory_Mass_Hyperplane_smul_mem_loc
-- name    : GlobalTheory.Mass.Hyperplane.smul_mem_loc
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:11:17.984442+00:00
-- url     : https://prove2.me/theorems/6b9bf5b1-9adf-4170-b1eb-894ca5575cf4
-- title:
--   Hyperplane: smul mem loc
-- statement:
--   The Hyperplane construction uses the smul mem loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/StarMemLocR.lean#L231-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/StarMemLocR.lean#L231-L239

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
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem GlobalTheory.Mass.Hyperplane.smul_mem_loc {P : Ideal (𝓞 K)} {M : Submodule (𝓞 K) V} {a : K} {x : V} (ha : a ∈ locR (K := K) P)
    (hx : x ∈ loc (K := K) P M) : a • x ∈ loc (K := K) P M := by sorry
