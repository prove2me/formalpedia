-- Prove2me | Theorems.Thm_N25_GlobalKummer_ramification_inputs
-- name    : N25.GlobalKummer.ramification_inputs
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:38:52.540778+00:00
-- url     : https://prove2.me/theorems/6f8d2de4-80f9-47a3-822a-4fd36e8afbd5
-- title:
--   The kernel representation is finite-dimensional and unramified outside $\{5,71\}$
-- statement:
--   Assume the cyclotomic relation and the frozen filtration of $V=\ker π$. Then $V$ is finite-dimensional over $𝔽_{71}$; every vector of $V$ is fixed by the Galois group of some finite extension of $ℚ$; and for every prime $q$ outside $S=\{5,71\}$, inertia at every place above $q$ acts trivially on $V$: $$\dim_{𝔽_{71}}V<\infty,\qquad \forall v\in V\ \exists F/ℚ\text{ finite}:G_Fv=v,\qquad ρ_V(I_q)=1\ (q\notin S).$$ These are the finiteness, continuity, and ramification inputs for continuous $S$-cohomology. Formalization note: the type of prime numbers used in the last clause carries primality as part of the object.
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

set_option autoImplicit false
noncomputable section
open N25
open N25.GlobalKummer
local instance instL_N25_GlobalKummer_ramification_inputs_23397f_iff16b7 : Fact (Nat.Prime 71) := ⟨by decide⟩

theorem N25.GlobalKummer.ramification_inputs (hPhi : PhiFiveZero) (K2 : K2Rows) :
    FiniteDimensional (ZMod 71) (vRep hPhi) ∧
      (∀ v : vRep hPhi, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ),
        FiniteDimensional ℚ F ∧ ∀ s ∈ F.fixingSubgroup, (vRep hPhi).ρ s v = v) ∧
      (∀ q : Nat.Primes, q ∉ ramificationSet →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (q : ℕ) →
          ∀ g ∈ A.inertiaSubgroupIn ℚ, (vRep hPhi).ρ g = 1) := by sorry
