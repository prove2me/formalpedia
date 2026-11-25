-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_adelicNorm_le_of_local
-- name    : GroundTheory.Automorphic.Reduction.adelicNorm_le_of_local
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:53:11.155564+00:00
-- url     : https://prove2.me/theorems/999736d0-e3b2-4296-8816-1a5ec0f5944f
-- title:
--   Reduction: adelic Norm le of local
-- statement:
--   The Reduction construction uses the adelic Norm le of local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionFinite.lean#L56-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionFinite.lean#L56-L88

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

theorem GroundTheory.Automorphic.Reduction.adelicNorm_le_of_local {y y' : Fin n → 𝔸[K]} (hy : HasFiniteContent y)
    (hy' : HasFiniteContent y') (a : InfinitePlace K → ℝ) (b : HeightOneSpectrum (𝓞 K) → ℝ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hinf : ∀ w, euclidNorm (infComp w y) ≤ a w * euclidNorm (infComp w y'))
    (hb1 : ∀ v, v ∉ S → b v = 1)
    (hfin : ∀ v, ‖finComp v y‖ ≤ b v * ‖finComp v y'‖) :
    adelicNorm y ≤ (∏ w, a w ^ w.mult) * (∏ v ∈ S, b v) * adelicNorm y' := by sorry
