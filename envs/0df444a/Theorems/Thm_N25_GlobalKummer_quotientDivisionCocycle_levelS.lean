-- Prove2me | Theorems.Thm_N25_GlobalKummer_quotientDivisionCocycle_levelS
-- name    : N25.GlobalKummer.quotientDivisionCocycle_levelS
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:38:41.801671+00:00
-- url     : https://prove2.me/theorems/f8ef0409-4a9c-4b89-874d-b119e0122df1
-- title:
--   The quotient division cocycle is unramified outside $5$ and $71$
-- statement:
--   Assume the cyclotomic relation and the frozen filtration, and let $P\in M$, $Q\in J$ satisfy $π(Q)=P$. Let $\bar c_{P,Q}=q\circ c_{P,Q}$ be the cyclotomic quotient of the division cocycle and let $S=\{5,71\}$. Then $$\bar c_{P,Q}\in Z^1_S(G_{ℚ},𝔽_{71}(χ_{71}))\quad\text{with finite-level continuity data}.$$ This prepares the quotient cocycle for the global Kummer and ramification argument. Formalization note: finite-level $S$-constancy records both continuity and unramifiedness away from $S$.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_GlobalKummerQuotient
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
open N25
open N25.GlobalKummer

theorem N25.GlobalKummer.quotientDivisionCocycle_levelS (hPhi : PhiFiveZero) (K2 : K2Rows)
    (P : ↥M) (Q : J) (hQ : piEnd Q = (P : J)) :
    groupCohomology.IsLevelConstantS₁ ramificationSet
      (quotientDivisionCocycle hPhi K2 P Q hQ) := by sorry
