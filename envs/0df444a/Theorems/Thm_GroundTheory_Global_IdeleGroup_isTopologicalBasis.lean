-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_isTopologicalBasis
-- name    : GroundTheory.Global.IdeleGroup.isTopologicalBasis
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:13.208912+00:00
-- url     : https://prove2.me/theorems/5f3dc87c-815b-4061-bbac-022ffd31e14f
-- title:
--   Idele Group: is Topological Basis
-- statement:
--   The Idele Group construction uses the is Topological Basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/IdeleBasis.lean#L106-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/IdeleBasis.lean#L106-L159

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_Adele_Topology
import Definitions.Def_GroundTheory_GlobalFields_Adele_IdeleBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology TopologicalSpace NumberField IsDedekindDomain
open scoped RestrictedProduct NumberField.AdeleRing
open GroundTheory GroundTheory.Global
open GroundTheory.Global.IdeleGroup
variable (K : Type*) [Field K] [NumberField K]

theorem GroundTheory.Global.IdeleGroup.isTopologicalBasis :
    IsTopologicalBasis {s : Set (IdeleGroup K) |
      ∃ (U : ∀ w : InfinitePlace K, Set (w.Completion)ˣ)
        (V : ∀ v : HeightOneSpectrum (𝓞 K), Set (v.adicCompletion K)ˣ),
        (∀ w, IsOpen (U w)) ∧ (∀ v, IsOpen (V v)) ∧
        (∀ᶠ v in cofinite, V v =
          ((Submonoid.ofClass (v.adicCompletionIntegers K)).units : Set (v.adicCompletion K)ˣ)) ∧
        s = {x | (∀ w, infiniteProj w x ∈ U w) ∧ ∀ v, finiteProj v x ∈ V v}} := by sorry
