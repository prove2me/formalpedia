-- Prove2me | Theorems.Thm_N25_GlobalKummer_quotient_zero_on_inertia
-- name    : N25.GlobalKummer.quotient_zero_on_inertia
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:38:26.843952+00:00
-- url     : https://prove2.me/theorems/92572f68-a85c-4ab0-b64c-1f89bd2de9cf
-- title:
--   The quotient cocycle vanishes on inertia away from $5$ and $71$
-- statement:
--   Assume the cyclotomic relation and the frozen filtration. Let $P\in M$, $Q\in J$ satisfy $π(Q)=P$. Let $ℓ$ be a prime with $ℓ\ne5,71$, let $A\subseteq ℚ̄$ be a valuation ring above $ℓ$, and let $σ\in I_A$. Then $$\bar c_{P,Q}(σ)=0.$$ This proves the ordinary unramified local condition at every prime outside the two-prime ramification set. Formalization note: the prime typeclass and the valuation-ring witness are Lean's explicit packaging of the chosen prime and place.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_GlobalKummerQuotient
import Definitions.Def_N25_KummerFactorization
import Definitions.Def_N25_LocalKummerEquivariance
import Theorems.Thm_ModularCurve_exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd
import Theorems.Thm_ModularCurve_reductionQExpModL_gammaH_smul_eq_self_of_mem_inertiaSubgroupIn
import Theorems.Thm_ModularCurve_eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero

set_option autoImplicit false
open N25
open N25.GlobalKummer

theorem N25.GlobalKummer.quotient_zero_on_inertia
    (hPhi : PhiFiveZero) (K2 : K2Rows)
    (P : ↥M) (Q : J) (hQ : piEnd Q = (P : J))
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : ℓ ≠ 5) (hℓ71 : ℓ ≠ 71)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (σ : Gal) (hσ : σ ∈ A.inertiaSubgroupIn ℚ) :
    quotientDivisionCocycle hPhi K2 P Q hQ σ = 0 := by sorry
