-- Prove2me | Theorems.Thm_OAI_Paper320_recursive_sensitivity_zero_at_sharp
-- name    : OAI.Paper320.recursive_sensitivity_zero_at_sharp
-- status  : Proved
-- author  : @Leo Shaposhnik
-- created : 2026-10-15T23:57:13.887986+00:00
-- url     : https://prove2.me/theorems/2fe8a088-c85c-4a78-8225-d26df1bfbce6
-- title:
--   Sharper sensitivity of the recursive predicate at a rejecting input
-- statement:
--   Let $k,r,h\in\mathbb N$, let $I$ be finite, let $T$ be a tournament on $[k]$, and let $A$ be a good $r$-labeling, with $r>0$. Let $F=(F_t)_{t\in[h+1]}$ be nested: acceptance at a larger index implies acceptance at every smaller index. Set $P_q=\mathrm{recursiveFamily}(T,A,F,q)$ on raw coordinates $([k]\times[r])\times I$.
--
--   For $b\in\{0,1\}$, let $S_b(F)$ be the maximum sensitivity of a family member at an input where it outputs $b$, and let $J_b(F)$ maximize the number of raw coordinate flips changing two distinct ordered members that both output $b$ at their common input. For every $q\in[h]$ and every $x$ with $P_q(x)=0$,
--   $$s(P_q,x)\le15S_0(F)+\max\{S_1(F)+J_1(F),\ 3J_1(F)\}.$$
--   The maximum follows from mutually exclusive sink and no-sink cases for the fixed gate-candidate set; it does not add the maxima from those incompatible cases.
-- source:
--   Local research commit f142fafe7b0ad4f46d209a530ee057421fe0f374, lean/round2-sharp/Sharp/RecursiveZero.lean, recursive_sensitivity_zero_at_sharp; new gate lemma in Sharp/Gates.lean and original OpenAI repair/candidate helpers. Built on OpenAI, A superquadratic separation between sensitivity and block sensitivity (September 25, 2026), source: https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity. Existing platform definitions are reused unchanged; supporting upstream helpers retain OpenAI attribution.

/-
GENERATED FILE — MODIFIED SOURCE NOTICE
Local proof source: block-sensitivity commit f142faf.
Upstream helper source: OpenAI/math commit
1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Original modules used in this file:
  lean/round2-sharp/Sharp/RecursiveZero.lean
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
import Theorems.Thm_OAI_Paper320_gateNonsinks_card_of_sink

open scoped Classical

theorem OAI.Paper320.recursive_sensitivity_zero_at_sharp :
  ∀ {k r h : ℕ} {I : Type} [inst : Fintype I] (T : OAI.Paper320.Tournament k) (A : OAI.Paper320.GoodLabeling T r)
  (F : Fin (h + 1) → (I → Bool) → Bool),
  OAI.Paper320.NestedFamily F →
    0 < r →
      ∀ (q : Fin h) (x : (Fin k × Fin r) × I → Bool),
        OAI.Paper320.recursiveFamily T A.label F q x = Bool.false →
          OAI.Paper320.sensitivityAt (OAI.Paper320.recursiveFamily T A.label F q) x ≤
            15 * OAI.Paper320.sideSensitivity F Bool.false +
              Max.max (OAI.Paper320.sideSensitivity F Bool.true + OAI.Paper320.jointSensitivity F Bool.true)
                (3 * OAI.Paper320.jointSensitivity F Bool.true) := by sorry
