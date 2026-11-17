-- Prove2me | Theorems.Thm_N25_GlobalKummer_exists_psiClass_of_quotient_zero
-- name    : N25.GlobalKummer.exists_psiClass_of_quotient_zero
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:38:33.613645+00:00
-- url     : https://prove2.me/theorems/abc500c8-4aa7-4152-8661-3f5eb740de7f
-- title:
--   A class with zero quotient lifts to the $ψ$-line
-- statement:
--   Assume the cyclotomic relation and the exact sequence $0\to 𝔽_{71}(ψ)\xrightarrow{i}V\xrightarrow{q}𝔽_{71}(χ_{71})\to0$. Let $S=\{5,71\}$ and let $x\in H^1_S(G_{ℚ},V)$ satisfy $q_*(x)=0$ in ordinary cohomology. Then there exists $a\in H^1_S(G_{ℚ},𝔽_{71}(ψ))$ such that $$i_*(a)=x\quad\text{in }H^1(G_{ℚ},V).$$ This is the continuous long-exact-sequence lift used to reduce the descent to the twisted one-dimensional character.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_GlobalKummerSequence
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
import Theorems.Thm_groupCohomology_exists_les_continuousHS_of_shortExact_of_isLevelConstant

set_option autoImplicit false
open N25
open N25.GlobalKummer

theorem N25.GlobalKummer.exists_psiClass_of_quotient_zero (hPhi : PhiFiveZero) (K2 : K2Rows)
    (x : ↥(groupCohomology.continuousH1S ramificationSet (vRep hPhi)))
    (hx : (groupCohomology.map (MonoidHom.id Gal) (kernelQuotient hPhi K2) 1).hom
      (x : groupCohomology.H1 (vRep hPhi)) = 0) :
    ∃ a : ↥(groupCohomology.continuousH1S ramificationSet psiRep),
      (groupCohomology.map (MonoidHom.id Gal) (kernelInclusion hPhi K2) 1).hom
        (a : groupCohomology.H1 psiRep) = (x : groupCohomology.H1 (vRep hPhi)) := by sorry
