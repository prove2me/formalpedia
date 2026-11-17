-- Prove2me | Theorems.Thm_N25_GlobalKummer_divisionClass_mem_continuousH1S
-- name    : N25.GlobalKummer.divisionClass_mem_continuousH1S
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:38:36.647193+00:00
-- url     : https://prove2.me/theorems/f4b98040-5b87-4a6f-803a-2953feaf7df2
-- title:
--   The division class is unramified outside $5$ and $71$
-- statement:
--   Let $J$ be the geometric Jacobian carrier, let $M=J^{G_{ℚ}}$, let $π:J\to J$ be the selected endomorphism, and put $V=\ker π$ with its $𝔽_{71}$-representation structure supplied by the cyclotomic relation. Assume the frozen exact filtration of $V$. For $P\in M$ and $Q\in J$ with $π(Q)=P$, define $c_{P,Q}(σ)=σQ-Q$. If $S$ consists of the primes $5$ and $71$, then $$[c_{P,Q}]\in H^1_S(G_{ℚ},V).$$ This places the division class in the Selmer-type continuous cohomology group used by the global descent. Formalization note: the hypotheses named by the cyclotomic relation and the frozen filtration package the representation and its exact sequence.
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
open N25
open N25.GlobalKummer

theorem N25.GlobalKummer.divisionClass_mem_continuousH1S (hPhi : PhiFiveZero) (K2 : K2Rows)
    (P : ↥M) (Q : J) (hQ : piEnd Q = (P : J)) :
    groupCohomology.H1π (vRep hPhi) (divisionCocycle hPhi P Q hQ) ∈
      groupCohomology.continuousH1S ramificationSet (vRep hPhi) := by sorry
