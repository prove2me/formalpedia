-- Prove2me | Theorems.Thm_N25_GlobalKummer_continuous_exact
-- name    : N25.GlobalKummer.continuous_exact
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:41:23.582852+00:00
-- url     : https://prove2.me/theorems/333304fd-1951-41a7-b687-897df16ffd03
-- title:
--   Exactness of continuous cohomology outside $5$ and $71$
-- statement:
--   Let $G=\operatorname{Gal}(\overline{\mathbf Q}/\mathbf Q)$, let $S=\{5,71\}$, let $\psi$ be the one-dimensional character occurring in the selected kernel, and let $\chi_{71}$ be the mod-$71$ cyclotomic character. Let $V=\ker(2+4\gamma+\gamma^2)$, assume $1+\gamma+\gamma^2+\gamma^3+\gamma^4=0$ on the Jacobian, and assume the supplied exact Galois-equivariant sequence $0\to\mathbf F_{71}(\psi)\to V\to\mathbf F_{71}(\chi_{71})\to0$. Then there are $\mathbf F_{71}$-linear maps induced by its inclusion and quotient such that
--
--   $$H^1_S(G,\mathbf F_{71}(\psi))\xrightarrow{i}H^1_S(G,V)\xrightarrow{q}H^1_S(G,\mathbf F_{71}(\chi_{71})),\qquad \operatorname{im}i=\ker q.$$
--
--   Moreover, after inclusion into ordinary $H^1$, $i$ and $q$ are exactly the cohomology maps induced by the stated kernel inclusion and quotient. This exactness is the global cohomological backbone of the Kummer descent. Formalization note: the hypotheses package the exactness and Galois-equivariance data, while the coercions from $H^1_S$ to ambient $H^1$ are bookkeeping.
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
noncomputable section
open CategoryTheory
open N25
open N25.GlobalKummer
local instance instL_N25_GlobalKummer_continuous_exact_23397f_i03e72d : Fact (Nat.Prime 71) := ⟨by decide⟩

theorem N25.GlobalKummer.continuous_exact (hPhi : PhiFiveZero) (K2 : K2Rows) :
    ∃ (i : ↥(groupCohomology.continuousH1S ramificationSet psiRep) →ₗ[ZMod 71]
          ↥(groupCohomology.continuousH1S ramificationSet (vRep hPhi)))
      (q : ↥(groupCohomology.continuousH1S ramificationSet (vRep hPhi)) →ₗ[ZMod 71]
          ↥(groupCohomology.continuousH1S ramificationSet cyclotomicRep)),
      (∀ x, (i x : groupCohomology.H1 (vRep hPhi)) =
        (groupCohomology.map (MonoidHom.id Gal) (kernelInclusion hPhi K2) 1).hom (x : groupCohomology.H1 psiRep)) ∧
      (∀ y, (q y : groupCohomology.H1 cyclotomicRep) =
        (groupCohomology.map (MonoidHom.id Gal) (kernelQuotient hPhi K2) 1).hom (y : groupCohomology.H1 (vRep hPhi))) ∧
      Function.Exact i q := by sorry
