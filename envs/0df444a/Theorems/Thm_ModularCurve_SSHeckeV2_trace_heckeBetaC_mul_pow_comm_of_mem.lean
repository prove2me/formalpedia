-- Prove2me | Theorems.Thm_ModularCurve_SSHeckeV2_trace_heckeBetaC_mul_pow_comm_of_mem
-- name    : ModularCurve.SSHeckeV2.trace_heckeBetaC_mul_pow_comm_of_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/a8df2488-fbd7-5bdf-b8c1-92cb0cd3fb95
-- title:
--   Commutativity of the trace Hecke operators on L(weightDivisor)
-- statement:
--   Fix a prime $p$ with $5 \le p$ and an algebraically closed field $K$ of characteristic $p$, a natural number $N \neq 0$ whose image in $K$ is nonzero, and two primes $\ell, \ell'$, neither dividing $N$ and neither equal to $p$. Let $F = K(j(q), j(q^N))$ be the intermediate field `modularFunctionFieldC K N` of the Laurent series field over $K$, and for a prime $q$ let $R_q = K(j(q), j(q^N), j(q^{q}), j(q^{Nq}))$ be `charLDegeneracyRoof K N q`, viewed as an $F$-algebra via the inclusion `heckeAlphaC` (the degeneracy map $\alpha_q$). Let $m \ge 1$ and let $G \in F$ lie in the Riemann–Roch space of the divisor `weightDivisor K N m`, i.e. $v(G) \le \exp(\mathrm{weightDivisor}(v))$ at every place $v$ of $F$ over $K$. Writing $T_q(X) = q^{m-1} \cdot \mathrm{Tr}_{R_q/F}\bigl(\beta_q(X)\, h_q^{\,m}\bigr)$, where $\beta_q$ is the substitution $q \mapsto q^{q}$ algebra map `heckeBetaC` and $h_q$ is `heckeMultiplier`, the element of $R_q$ comparing $d(\beta_q j)$ with the image of $dj$, the conclusion is $T_\ell(T_{\ell'} G) = T_{\ell'}(T_\ell G)$. No membership hypothesis is imposed on the intermediate values $T_{\ell'} G$, $T_\ell G$.
--
--   This is the commutativity of the weight-$2m$ Hecke correspondences at two primes of good reduction, in the form of trace operators along the degeneracy maps of the modular function field in characteristic $p$. It supplies the commuting-family input used by [`ModularCurve.SSHeckeV2.ssHeckeFun_window`](thm.html#ModularCurve.SSHeckeV2.ssHeckeFun_window) and by [`ModularCurve.SSHeckeV2.exists_omegaHecke_dualMap_theta_and_exit`](thm.html#ModularCurve.SSHeckeV2.exists_omegaHecke_dualMap_theta_and_exit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_SSHeckeV2_trace_heckeBetaC_mul_pow_comm_of_mem.lean

import Mathlib
import Definitions.Def_ModularCurve_SSCarrier
import Definitions.Def_ModularCurve_SSHeckeV2
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open AlgebraicCurve ModularCurve

theorem ModularCurve.SSHeckeV2.trace_heckeBetaC_mul_pow_comm_of_mem
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]
    (hN : (N : K) ≠ 0) (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (hℓp : ℓ ≠ p) (ℓ' : ℕ) [Fact ℓ'.Prime] (hℓ'N : ¬ ℓ' ∣ N) (hℓ'p : ℓ' ≠ p)
    (m : ℕ) (hm : 1 ≤ m) (G : ↥(modularFunctionFieldC K N))
    (hG : G ∈ AlgebraicCurve.riemannRochSpace (ModularCurve.weightDivisor K N m)) :
    (letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ)
     letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ')
     algebraMap K ↥(modularFunctionFieldC K N) ((ℓ : K) ^ (m - 1)) *
        Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ)
          (heckeBetaC K N ℓ
              (algebraMap K ↥(modularFunctionFieldC K N) ((ℓ' : K) ^ (m - 1)) *
                Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ')
                  (heckeBetaC K N ℓ' G * ModularCurve.heckeMultiplier N K ℓ' ^ m))
            * ModularCurve.heckeMultiplier N K ℓ ^ m)
     = algebraMap K ↥(modularFunctionFieldC K N) ((ℓ' : K) ^ (m - 1)) *
        Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ')
          (heckeBetaC K N ℓ'
              (algebraMap K ↥(modularFunctionFieldC K N) ((ℓ : K) ^ (m - 1)) *
                Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ)
                  (heckeBetaC K N ℓ G * ModularCurve.heckeMultiplier N K ℓ ^ m))
            * ModularCurve.heckeMultiplier N K ℓ' ^ m)) := by sorry
