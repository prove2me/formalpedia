-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleMap_existsUnique_ideleMap
-- name    : GroundTheory.Global.IdeleMap.existsUnique_ideleMap
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:55:01.456162+00:00
-- url     : https://prove2.me/theorems/7c040c30-d618-5597-9b38-18eb1a621ba7
-- title:
--   Idele Map: exists Unique idele Map
-- statement:
--   The Idele Map construction uses the exists Unique idele Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/NormResidueSymbol/AbstractUnique.lean#L116-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/NormResidueSymbol/AbstractUnique.lean#L116-L122

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_NormResidueSymbol_Abstract
import Definitions.Def_GroundTheory_GlobalFields_NormResidueSymbol_AbstractUnique
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
  [TopologicalSpace G] [DiscreteTopology G]
  (φ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* G)
  (φinf : ∀ w : InfinitePlace K, (w.Completion)ˣ →* G)
  (hφ : ∀ᶠ v in cofinite,
    (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤ (φ v).ker)
include hφ

theorem GroundTheory.Global.IdeleMap.existsUnique_ideleMap (hφc : ∀ v, Continuous (φ v))
    (hφinfc : ∀ w, Continuous (φinf w)) :
    ∃! ψ : IdeleGroup K →* G, Continuous ψ ∧ (∀ v, ψ.comp (finiteEmbedding v) = φ v) ∧
      ∀ w, ψ.comp (infiniteEmbedding w) = φinf w := by sorry
