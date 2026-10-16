-- Prove2me | Theorems.Thm_OAI_Paper320_finite_certificate_20205
-- name    : OAI.Paper320.finite_certificate_20205
-- status  : Proved
-- author  : @Leo Shaposhnik
-- created : 2026-10-16T00:07:13.698245+00:00
-- url     : https://prove2.me/theorems/9dd8ebf2-b8ba-46a5-8d03-d399fad85a88
-- title:
--   A finite total Boolean seed certifying exponent 2.0205
-- statement:
--   Set $M=1475863$, $r=88$, $K=1439236$, $k=2M^2+1$, and let
--   $$(a,b,c,e)=\mathrm{sharpBounds}(M,r,19,17),\qquad A=\max(Ka,b),\qquad B=KMk^{17}.$$
--   Here `sharpBounds` starts at $(19,19M,0,0)$ and iterates the simultaneous sharper four-profile recurrence for $17$ steps. There exist a positive integer $n$ and a total Boolean function $f:\{0,1\}^n\to\{0,1\}$ such that
--   $$f(0)=0,\qquad s(f)\le A,\qquad \operatorname{bs}(f,0)\ge B,$$
--   $$1<A,\qquad A^2<B,\qquad A^{4041}<B^{2000}.$$
--   Sensitivity $s(f)$ is maximized over all inputs. Block sensitivity at zero counts a maximum family of pairwise disjoint, nonempty blocks whose flips change $f(0)$. Every displayed arithmetic comparison is exact. Since $4041/2000=2.0205$, this provides the finite input to the campaign's existing finite-to-asymptotic certificate theorem; that later deduction is separate from this theorem.
-- source:
--   Local research commit f142fafe7b0ad4f46d209a530ee057421fe0f374, lean/round2-sharp/Sharp/Certificate.lean, finite_certificate_20205; seed/majorant/arithmetic proofs in Sharp/Seed.lean, Profiles.lean, Arithmetic.lean; general OR construction Round2/GeneralSeed.lean; original OpenAI coordinate, ball-predicate and disjoint-block helpers. Built on OpenAI, A superquadratic separation between sensitivity and block sensitivity (September 25, 2026), source: https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity. Existing platform definitions are reused unchanged; supporting upstream helpers retain OpenAI attribution.

/-
GENERATED FILE — MODIFIED SOURCE NOTICE
Local proof source: block-sensitivity commit f142faf.
Upstream helper source: OpenAI/math commit
1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Original modules used in this file:
  lean/round2-sharp/Sharp/Certificate.lean
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
import Theorems.Thm_OAI_Paper320_Tournament_goodLabeling_exists_of_power_bound
import Theorems.Thm_OAI_Paper320_tower_four_recurrences_sharp

open scoped Classical

theorem OAI.Paper320.finite_certificate_20205 :
  ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
  0 < n ∧
    (f fun (x : Fin n) => Bool.false) = Bool.false ∧
      OAI.Paper320.sensitivity f ≤ OAI.Paper320.sharpA ∧
        (OAI.Paper320.sharpB ≤ OAI.Paper320.blockSensitivityAt f fun (x : Fin n) => Bool.false) ∧
          1 < OAI.Paper320.sharpA ∧
            OAI.Paper320.sharpA ^ 2 < OAI.Paper320.sharpB ∧ OAI.Paper320.sharpA ^ 4041 < OAI.Paper320.sharpB ^ 2000 := by sorry
