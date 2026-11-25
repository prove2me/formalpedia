-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_expG_smul_mem_maxCompact_complex
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.expG_smul_mem_maxCompact_complex
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:27:44.57892+00:00
-- url     : https://prove2.me/theorems/97cc2618-b917-48da-bded-3ca34dd010bd
-- title:
--   Is Exp Lie Algebra: exp G smul mem max Compact complex
-- statement:
--   The Is Exp Lie Algebra construction uses the exp G smul mem max Compact complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/CartanBasis.lean#L318-L325
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/CartanBasis.lean#L318-L325

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

theorem GroundTheory.Automorphic.IsExpLieAlgebra.expG_smul_mem_maxCompact_complex {G : Subgroup (Matrix ι ι ℂ)ˣ}
    {𝔤 : Submodule ℝ (Matrix ι ι ℂ)} (h : IsExpLieAlgebra G 𝔤) {X : 𝔤}
    (hX : (X : Matrix ι ι ℂ)ᴴ = -(X : Matrix ι ι ℂ)) (t : ℝ) :
    h.expG (t • X) ∈ maxCompact G := by sorry
