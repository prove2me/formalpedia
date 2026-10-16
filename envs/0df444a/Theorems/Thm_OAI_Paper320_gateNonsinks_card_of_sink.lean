-- Prove2me | Theorems.Thm_OAI_Paper320_gateNonsinks_card_of_sink
-- name    : OAI.Paper320.gateNonsinks_card_of_sink
-- status  : Proved
-- author  : @Leo Shaposhnik
-- created : 2026-10-15T23:53:30.075162+00:00
-- url     : https://prove2.me/theorems/a2abf484-2d18-4191-b273-5fa8fc1ba422
-- title:
--   A gate-candidate tournament with a sink has at most one nonsink
-- statement:
--   Let $k,r,h\in\mathbb N$, let $I$ be any type, let $T$ be a tournament on $[k]$, and let $\ell:[k]\times[k]\to[r]$ be any labeling. Let $F=(F_t)_{t\in[h+1]}$ be a nested family of total Boolean predicates on $\{0,1\}^I$. Fix $q\in[h]$ and an input $x$ on $([k]\times[r])\times I$.
--
--   Let $G=\mathrm{gateCandidates}(T,\ell,F,q,x)$ be the rows whose clause has no failed target and exactly one failed gate. Let $S\subseteq G$ consist of vertices with no outgoing edge to any member of $G$, namely the existing set `gateSinks`. If $S\ne\varnothing$, then
--   $$|G\setminus S|\le1.$$
--   No good-labeling assumption or positivity assumption on $r$ is required. This structural bound separates the sink case from the three-vertex cycle case in the sharpened ordinary zero-input recurrence.
-- source:
--   Local research commit f142fafe7b0ad4f46d209a530ee057421fe0f374, lean/round2-sharp/Sharp/Gates.lean, gateNonsinks_card_of_sink; upstream helper proofs from Tournament, RecursiveCandidates, RecursiveFailures and RecursiveDefinitions. Built on OpenAI, A superquadratic separation between sensitivity and block sensitivity (September 25, 2026), source: https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity. Existing platform definitions are reused unchanged; supporting upstream helpers retain OpenAI attribution.

/-
GENERATED FILE — MODIFIED SOURCE NOTICE
Local proof source: block-sensitivity commit f142faf.
Upstream helper source: OpenAI/math commit
1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Original modules used in this file:
  lean/round2-sharp/Sharp/Gates.lean
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

theorem OAI.Paper320.gateNonsinks_card_of_sink :
  ∀ {k r h : ℕ} {I : Type} (T : OAI.Paper320.Tournament k) (label : Fin k → Fin k → Fin r)
  (F : Fin (h + 1) → (I → Bool) → Bool),
  OAI.Paper320.NestedFamily F →
    ∀ (q : Fin h) (x : (Fin k × Fin r) × I → Bool),
      (OAI.Paper320.gateSinks T label F q x).Nonempty →
        (OAI.Paper320.gateCandidates T label F q x \ OAI.Paper320.gateSinks T label F q x).card ≤ 1 := by sorry
