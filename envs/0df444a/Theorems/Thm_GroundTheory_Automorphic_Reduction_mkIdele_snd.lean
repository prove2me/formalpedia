-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_mkIdele_snd
-- name    : GroundTheory.Automorphic.Reduction.mkIdele_snd
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:05:25.093801+00:00
-- url     : https://prove2.me/theorems/1b77ae97-8dca-4bb5-867e-e328408358c2
-- title:
--   Reduction: mk Idele snd
-- statement:
--   The Reduction construction uses the mk Idele snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionFinite.lean#L234-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionFinite.lean#L234-L239

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIdele
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory.Global GroundTheory.Global.IdeleGroup
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem GroundTheory.Automorphic.Reduction.mkIdele_snd (a : ∀ w : InfinitePlace K, w.Completion)
    (b : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K) (ha : ∀ w, a w ≠ 0) (hb : ∀ v, b v ≠ 0)
    (hb1 : ∀ᶠ v in cofinite, ‖b v‖ = 1) (v : HeightOneSpectrum (𝓞 K)) :
    ((mkIdele a b ha hb hb1 : IdeleGroup K) : 𝔸[K]).2 v = b v := by sorry
