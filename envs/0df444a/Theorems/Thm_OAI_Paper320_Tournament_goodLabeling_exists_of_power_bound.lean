-- Prove2me | Theorems.Thm_OAI_Paper320_Tournament_goodLabeling_exists_of_power_bound
-- name    : OAI.Paper320.Tournament.goodLabeling_exists_of_power_bound
-- status  : Proved
-- author  : @Leo Shaposhnik
-- created : 2026-10-15T23:53:21.594235+00:00
-- url     : https://prove2.me/theorems/50f9434c-b214-422a-9280-fb205641130d
-- title:
--   Good tournament labelings from an exact power bound
-- statement:
--   Let $k,r\in\mathbb N$, and let $T$ be a tournament on $[k]$. Assume $r>0$, $120\le k^2$, and
--   $$k^{16}<r^{104}.$$
--   Then there is a labeling $A:[k]\times[k]\to[r]$ such that every set $U\subseteq[k]$ of $16$ vertices and every target-label map $m:[k]\to[r]$ admit an internal directed edge $i\to j$ with
--   $$A(i,j)\ne m(j).$$
--   Thus no $16$-vertex set has every internal edge labeled by the target assigned to its head. This is exactly nonemptiness of the existing `GoodLabeling T r` structure. The explicit power hypothesis permits label alphabets smaller than the convenient square-root choice used elsewhere.
-- source:
--   OpenAI, A superquadratic separation between sensitivity and block sensitivity, Lemma 2.1; original Lean theorem goodLabeling_exists_of_power_bound: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/Labeling.lean . Reused proof preserved in local commit f142fafe7b0ad4f46d209a530ee057421fe0f374, lean/round2/OAI/Combinatorics/Sensitivity/Labeling.lean; only import adaptation is needed for the platform.

/-
GENERATED FILE — MODIFIED SOURCE NOTICE
Local proof source: block-sensitivity commit f142faf.
Upstream helper source: OpenAI/math commit
1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Original modules used in this file:
  lean/round2/OAI/Combinatorics/Sensitivity/Labeling.lean
Modifications: mechanical skeleton subtraction, import rewriting,
and a root solution alias with the same elaborated theorem type.
Copied upstream files previously received only the documented Lean
conditional-proof lemma-name port; mathematical definitions and
statements were preserved. This generated file is local staging.
-/

import Mathlib
import Definitions.Def_OAI_Combinatorics_Sensitivity_Basic
import Definitions.Def_OAI_Combinatorics_Sensitivity_Composition
import Definitions.Def_OAI_Combinatorics_Sensitivity_Construction
import Definitions.Def_OAI_Combinatorics_Sensitivity_FixedCoordinates
import Definitions.Def_OAI_Combinatorics_Sensitivity_HammingBase
import Definitions.Def_OAI_Combinatorics_Sensitivity_InitialPredicates
import Definitions.Def_OAI_Combinatorics_Sensitivity_Iterates
import Definitions.Def_OAI_Combinatorics_Sensitivity_LabelingEvents
import Definitions.Def_OAI_Combinatorics_Sensitivity_Or
import Definitions.Def_OAI_Combinatorics_Sensitivity_ProfileArithmetic
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveBlocks
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveCandidates
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveDefinitions
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveFailures
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveSets
import Definitions.Def_OAI_Combinatorics_Sensitivity_Reindex
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tournament
import Definitions.Def_OAI_Combinatorics_Sensitivity_TournamentCounts
import Definitions.Def_OAI_Combinatorics_Sensitivity_TournamentCyclic
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tower
import Definitions.Def_OAI_Combinatorics_Sensitivity_TowerProfiles
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Theorems.Thm_OAI_Paper320_Tournament_card_badLabelings_le
import Theorems.Thm_OAI_Paper320_Tournament_card_internalEdges
import Theorems.Thm_OAI_Paper320_Tournament_card_le_three_of_outdegree_le_one
import Theorems.Thm_OAI_Paper320_Tournament_labelingConstraint_iff
import Theorems.Thm_OAI_Paper320_ballPredicate_sensitivityAt_zero_le
import Theorems.Thm_OAI_Paper320_blockSensitivityAt_compose_zero_le
import Theorems.Thm_OAI_Paper320_coupled_profiles_bound
import Theorems.Thm_OAI_Paper320_exists_blockSensitivityAt_family
import Theorems.Thm_OAI_Paper320_initialFamily_joint
import Theorems.Thm_OAI_Paper320_le_blockSensitivityAt_of_family
import Theorems.Thm_OAI_Paper320_normalized_profiles_step
import Theorems.Thm_OAI_Paper320_quantitative_profile_bounds
import Theorems.Thm_OAI_Paper320_quantitative_separation
import Theorems.Thm_OAI_Paper320_recursive_joint_one_at
import Theorems.Thm_OAI_Paper320_recursive_joint_zero_at
import Theorems.Thm_OAI_Paper320_recursive_sensitivity_one_at
import Theorems.Thm_OAI_Paper320_recursive_sensitivity_zero_at
import Theorems.Thm_OAI_Paper320_rowClause_repair_cases
import Theorems.Thm_OAI_Paper320_sensitivity_orCopies_le
import Theorems.Thm_OAI_Paper320_towerFamily_blocks
import Theorems.Thm_OAI_Paper320_tower_four_recurrences
import Theorems.Thm_SensitivityCampaign_baseline
import Theorems.Thm_SensitivityCampaign_baseline_arithmetic
import Theorems.Thm_SensitivityCampaign_finite_certificate
import Theorems.Thm_SensitivityCampaign_openai_seed_bounds
import Definitions.Def_BS20205_Round2_Bounds
import Definitions.Def_BS20205_Round2_GeneralSeed
import Definitions.Def_BS20205_Sharp_Bounds
import Definitions.Def_BS20205_Sharp_Arithmetic

open scoped Classical

theorem OAI.Paper320.Tournament.goodLabeling_exists_of_power_bound :
  ∀ {k r : ℕ} (T : OAI.Paper320.Tournament k),
  0 < r → 120 ≤ k * k → k ^ 16 < r ^ 104 → Nonempty (OAI.Paper320.GoodLabeling T r) := by sorry
