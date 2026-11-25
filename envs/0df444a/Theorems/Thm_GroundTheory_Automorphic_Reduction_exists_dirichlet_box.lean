-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_exists_dirichlet_box
-- name    : GroundTheory.Automorphic.Reduction.exists_dirichlet_box
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:03:40.630877+00:00
-- url     : https://prove2.me/theorems/f72e09c1-a0c0-5498-98ba-5d67d19021de
-- title:
--   Reduction: exists dirichlet box
-- statement:
--   The Reduction construction uses the exists dirichlet box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionDirichlet.lean#L62-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionDirichlet.lean#L62-L204

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIdele
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalConditionIndex
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionDirichlet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K]
open scoped Classical

theorem GroundTheory.Automorphic.Reduction.exists_dirichlet_box : ∃ B : ℝ, 0 < B ∧ ∀ (a : 𝔸[K]) (N : ℕ), 0 < N →
    ∃ l : 𝓞 K, l ≠ 0 ∧
      (∀ w : InfinitePlace K, ‖(algebraMap K 𝔸[K] (l : K)).1 w‖ ≤ (N + 1) * B) ∧
      ∃ c : K, (∀ v : HeightOneSpectrum (𝓞 K),
          ‖(algebraMap K 𝔸[K] (l : K) * a + algebraMap K 𝔸[K] c).2 v‖ ≤ 1) ∧
        ∀ w : InfinitePlace K,
          ‖(algebraMap K 𝔸[K] (l : K) * a + algebraMap K 𝔸[K] c).1 w‖ ≤ B / N := by sorry
