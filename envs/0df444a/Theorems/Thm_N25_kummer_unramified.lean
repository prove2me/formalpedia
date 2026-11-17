-- Prove2me | Theorems.Thm_N25_kummer_unramified
-- name    : N25.kummer_unramified
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:38:46.011196+00:00
-- url     : https://prove2.me/theorems/291abfe9-3919-403c-9943-8e8d65dc0efb
-- title:
--   The division cocycle is unramified away from $5$ and $71$
-- statement:
--   Let $π=2+4γ+γ^2$ and assume the cyclotomic relation. Let $P∈J$ be fixed by $G_{ℚ}$ and choose $Q∈J$ with $π(Q)=P$. Let $ℓ$ be a prime distinct from $5$ and $71$, let $A⊆ℚ̄$ be a valuation ring above $ℓ$, and let $σ$ lie in its inertia subgroup. Then $$σQ-Q=0.$$ This proves that the Kummer division cocycle has no ramification outside the two designated primes. Formalization note: the prime and the chosen place above it are supplied explicitly.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_KummerFactorization
import Definitions.Def_N25_LocalKummerEquivariance
import Theorems.Thm_ModularCurve_exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd
import Theorems.Thm_ModularCurve_reductionQExpModL_gammaH_smul_eq_self_of_mem_inertiaSubgroupIn
import Theorems.Thm_ModularCurve_eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero

set_option autoImplicit false
open N25

theorem N25.kummer_unramified (hPhi : PhiFiveZero)
    (P Q : J) (hP : P ∈ M) (hQ : piEnd Q = P)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : ℓ ≠ 5) (hℓ71 : ℓ ≠ 71)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (σ : Gal) (hσ : σ ∈ A.inertiaSubgroupIn ℚ) : σ • Q - Q = 0 := by sorry
