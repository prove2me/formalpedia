-- Prove2me | Theorems.Thm_OAI_Paper320_tower_four_recurrences_sharp
-- name    : OAI.Paper320.tower_four_recurrences_sharp
-- status  : Proved
-- author  : @Leo Shaposhnik
-- created : 2026-10-16T00:03:01.612811+00:00
-- url     : https://prove2.me/theorems/e74663d9-cdc8-47da-826c-b1d87f1771a0
-- title:
--   Four sharpened profile bounds through one tournament-tower step
-- statement:
--   Let $M,r\in\mathbb N$, let $I$ be finite, let $T$ be a regular tournament on $2M^2+1$ vertices with outdegree $M^2$, and let $A$ be a good $r$-labeling, with $r>0$. For every $h\in\mathbb N$, let $\mathrm{base}(h)$ be an $h$-member family of Boolean predicates on $\{0,1\}^I$. Fix $D,n\in\mathbb N$ with $n<D$, and assume only that $\mathrm{base}(D)$ is nested.
--
--   At depth $n$, put $S_b=\mathrm{towerSide}(T,A,\mathrm{base},D,n,b)$ and $J_b=\mathrm{towerJoint}(T,A,\mathrm{base},D,n,b)$ for $b\in\{0,1\}$; these are the maximum side and same-input joint sensitivities of the depth-$n$ tower with $D-n$ remaining indices. Use primes for the corresponding quantities at depth $n+1$. Then
--   $$S'_1\le M^2S_0+rS_1,\qquad J'_1\le M^2J_0+rS_1,$$
--   $$S'_0\le15S_0+\max\{S_1+J_1,3J_1\},\qquad J'_0\le15S_0+3J_1.$$
--   The one-side bounds are retained from the original construction. The two rejecting-side bounds use the sharper fixed-clause analysis, enabling simultaneous induction on all four profiles.
-- source:
--   Local research commit f142fafe7b0ad4f46d209a530ee057421fe0f374, lean/round2-sharp/Sharp/Tower.lean, tower_four_recurrences_sharp; original OpenAI one-side and nesting helpers. Built on OpenAI, A superquadratic separation between sensitivity and block sensitivity (September 25, 2026), source: https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity. Existing platform definitions are reused unchanged; supporting upstream helpers retain OpenAI attribution.

/-
GENERATED FILE — MODIFIED SOURCE NOTICE
Local proof source: block-sensitivity commit f142faf.
Upstream helper source: OpenAI/math commit
1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Original modules used in this file:
  lean/round2-sharp/Sharp/Tower.lean
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
import Theorems.Thm_OAI_Paper320_recursive_joint_zero_at_sharp
import Theorems.Thm_OAI_Paper320_recursive_sensitivity_zero_at_sharp

open scoped Classical

theorem OAI.Paper320.tower_four_recurrences_sharp :
  ∀ {M r : ℕ} {I : Type} [inst : Fintype I] (T : OAI.Paper320.RegularTournament M)
  (A : OAI.Paper320.GoodLabeling T.toTournament r) (base : (h : ℕ) → Fin h → (I → Bool) → Bool) (D n : ℕ),
  n < D →
    0 < r →
      OAI.Paper320.NestedFamily (base D) →
        OAI.Paper320.towerSide T.toTournament A.label base D (n + 1) Bool.true ≤
            M ^ 2 * OAI.Paper320.towerSide T.toTournament A.label base D n Bool.false +
              r * OAI.Paper320.towerSide T.toTournament A.label base D n Bool.true ∧
          OAI.Paper320.towerJoint T.toTournament A.label base D (n + 1) Bool.true ≤
              M ^ 2 * OAI.Paper320.towerJoint T.toTournament A.label base D n Bool.false +
                r * OAI.Paper320.towerSide T.toTournament A.label base D n Bool.true ∧
            OAI.Paper320.towerSide T.toTournament A.label base D (n + 1) Bool.false ≤
                15 * OAI.Paper320.towerSide T.toTournament A.label base D n Bool.false +
                  Max.max
                    (OAI.Paper320.towerSide T.toTournament A.label base D n Bool.true +
                      OAI.Paper320.towerJoint T.toTournament A.label base D n Bool.true)
                    (3 * OAI.Paper320.towerJoint T.toTournament A.label base D n Bool.true) ∧
              OAI.Paper320.towerJoint T.toTournament A.label base D (n + 1) Bool.false ≤
                15 * OAI.Paper320.towerSide T.toTournament A.label base D n Bool.false +
                  3 * OAI.Paper320.towerJoint T.toTournament A.label base D n Bool.true := by sorry
