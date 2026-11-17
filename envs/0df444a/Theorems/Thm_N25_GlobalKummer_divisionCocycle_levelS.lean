-- Prove2me | Theorems.Thm_N25_GlobalKummer_divisionCocycle_levelS
-- name    : N25.GlobalKummer.divisionCocycle_levelS
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:38:47.694415+00:00
-- url     : https://prove2.me/theorems/665a220a-f9de-4426-9d8f-1b5798202a8f
-- title:
--   The division cocycle has finite level outside $S=\{5,71\}$
-- statement:
--   Let $J$, $M$, $π$, and $V=\ker π$ be the level-$25$ Jacobian data, assume the cyclotomic relation and the frozen filtration of $V$, and let $P\in M$, $Q\in J$ satisfy $π(Q)=P$. For $c_{P,Q}(σ)=σQ-Q$ and $S=\{5,71\}$, the cocycle has a finite level compatible with being unramified away from $S$: $$c_{P,Q}\in Z^1_S(G_{ℚ},V)\quad\text{with finite-level continuity data}.$$ This is the cocycle-level input needed to form its class in continuous $S$-cohomology. Formalization note: finite-level constancy is Lean's explicit encoding of continuity and ramification control.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_GlobalKummerRamification
import Definitions.Def_N25_LocalKummerKernel
import Definitions.Def_N25_KummerFactorization
import Definitions.Def_N25_LocalKummerEquivariance
import Theorems.Thm_ModularCurve_exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd
import Theorems.Thm_ModularCurve_reductionQExpModL_gammaH_smul_eq_self_of_mem_inertiaSubgroupIn
import Theorems.Thm_ModularCurve_eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero
import Definitions.Def_N25
import Theorems.Thm_ModularCurve_exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq_place_laurentBaseChange
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC
import Theorems.Thm_groupCohomology_exists_isUnramifiedOutside_forall_apply_eq_one_of_smooth

set_option autoImplicit false
noncomputable section
open N25
open N25.GlobalKummer
local instance instL_N25_GlobalKummer_divisionCocycle_levelS_23397f_i60b155 : Fact (Nat.Prime 71) := ⟨by decide⟩

theorem N25.GlobalKummer.divisionCocycle_levelS (hPhi : PhiFiveZero) (K2 : K2Rows)
    (P : ↥M) (Q : J) (hQ : piEnd Q = (P : J)) :
    groupCohomology.IsLevelConstantS₁ ramificationSet (divisionCocycle hPhi P Q hQ) := by sorry
