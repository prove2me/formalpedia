-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_expG_smul_mem_maxCompact_real
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.expG_smul_mem_maxCompact_real
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:27:45.999444+00:00
-- url     : https://prove2.me/theorems/c08de53b-eb34-46f0-a81b-df73b296e39d
-- title:
--   Is Exp Lie Algebra: exp G smul mem max Compact real
-- statement:
--   The Is Exp Lie Algebra construction uses the exp G smul mem max Compact real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/CartanBasis.lean#L309-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/CartanBasis.lean#L309-L316

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_CartanBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Matrix
set_option linter.unusedSectionVars false
attribute [local instance 100] LieRing.ofAssociativeRing
open NormedSpace
open scoped Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem GroundTheory.Automorphic.IsExpLieAlgebra.expG_smul_mem_maxCompact_real {G : Subgroup (Matrix ι ι ℝ)ˣ}
    {𝔤 : Submodule ℝ (Matrix ι ι ℝ)} (h : IsExpLieAlgebra G 𝔤) {X : 𝔤}
    (hX : (X : Matrix ι ι ℝ)ᴴ = -(X : Matrix ι ι ℝ)) (t : ℝ) :
    h.expG (t • X) ∈ maxCompact G := by sorry
