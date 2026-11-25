-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_exists_cartanData_real
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.exists_cartanData_real
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:27:24.960012+00:00
-- url     : https://prove2.me/theorems/3b309cfc-621b-4ac2-829e-7dbc406baeaf
-- title:
--   Is Exp Lie Algebra: exists cartan Data real
-- statement:
--   The Is Exp Lie Algebra construction uses the exists cartan Data real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/CartanBasis.lean#L327-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/CartanBasis.lean#L327-L334

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

theorem GroundTheory.Automorphic.IsExpLieAlgebra.exists_cartanData_real {G : Subgroup (Matrix ι ι ℝ)ˣ}
    {𝔤 : Submodule ℝ (Matrix ι ι ℝ)} (h : IsExpLieAlgebra G 𝔤) (hstar : ∀ X ∈ 𝔤, Xᴴ ∈ 𝔤) :
    ∃ (d : ℕ) (b : Module.Basis (Fin d) ℝ h.lieSubalgebra) (ε : Fin d → ℝ),
      (∀ i, ε i = 1 ∨ ε i = -1) ∧
      (∀ i j, traceForm h.lieSubalgebra (b i) (b j) = if i = j then ε i else 0) ∧
      ∀ i, ε i = -1 → ∀ t : ℝ, h.expG (t • h.ofLie (b i)) ∈ maxCompact G := by sorry
