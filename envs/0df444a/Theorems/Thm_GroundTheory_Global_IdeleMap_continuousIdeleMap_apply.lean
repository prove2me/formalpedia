-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleMap_continuousIdeleMap_apply
-- name    : GroundTheory.Global.IdeleMap.continuousIdeleMap_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:37:44.368161+00:00
-- url     : https://prove2.me/theorems/53313654-d972-4cad-b2ab-90cb649634f4
-- title:
--   Idele Map: continuous Idele Map apply
-- statement:
--   The Idele Map construction uses the continuous Idele Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/NormResidueSymbol/Abstract.lean#L126-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/NormResidueSymbol/Abstract.lean#L126-L129

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_Adele_IdeleBasis
import Definitions.Def_GroundTheory_GlobalFields_NormResidueSymbol_Abstract
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Filter Topology NumberField IsDedekindDomain
open scoped NumberField.AdeleRing
noncomputable section
open GroundTheory.Global.IdeleMap
open IdeleGroup
variable {K : Type*} [Field K] [NumberField K] {G : Type*} [CommGroup G]
  (φ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* G)
  (φinf : ∀ w : InfinitePlace K, (w.Completion)ˣ →* G)
variable (hφ : ∀ᶠ v in cofinite,
  (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤ (φ v).ker)
variable [TopologicalSpace G] [DiscreteTopology G]

theorem GroundTheory.Global.IdeleMap.continuousIdeleMap_apply (hφc : ∀ v, Continuous (φ v))
    (hφinfc : ∀ w, Continuous (φinf w)) (x : IdeleGroup K) :
    continuousIdeleMap φ φinf hφ hφc hφinfc x = ideleMap φ φinf hφ x := by sorry

attribute [defeq] GroundTheory.Global.IdeleMap.continuousIdeleMap_apply
