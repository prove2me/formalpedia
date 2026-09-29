-- Prove2me | Theorems.Thm_ModularCurve_exists_divisor_degree_weight_and_isIntegral_of_mem_riemannRochSpace
-- name    : ModularCurve.exists_divisor_degree_weight_and_isIntegral_of_mem_riemannRochSpace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/7c8c2611-3f75-5f50-8620-bbc353cafd33
-- title:
--   A weight-2m divisor on X₀(N)_ℚ̄ with integrality
-- statement:
--   Let $N\ge 1$ (a natural number with `NeZero N`) and let $m$ be a natural number with $1\le m$. Write $\bar F_N$ for [`ModularCurve.modularFunctionFieldBar N`](def/ModularCurve_ArithmeticGalois.html#L111), the intermediate field of $\overline{\mathbb Q}((q))$ generated over $\overline{\mathbb Q}$ by the coefficientwise image of `modularFunctionFieldFull N`, itself the subfield of $\mathbb Q((q))$ generated over $\mathbb Q$ by the divisor expansions attached to $N$, and write $\bar\jmath=$ `jBar N` for the element of $\bar F_N$ given by the $q$-expansion of $j$. Put $g=$ `genusFormula N` $=1+\psi(N)/12-\nu_2/4-\nu_3/3-\nu_\infty/2$, where $\psi(N)=\sum_{d\mid N,\ d\ \text{squarefree}}N/d$, $\nu_2=\#\{x\in\mathbb Z/N:x^2+1=0\}$, $\nu_3=\#\{x\in\mathbb Z/N:x^2+x+1=0\}$ and $\nu_\infty=$ `cuspCount N` $=\sum_{d\mid N}\varphi(\gcd(d,N/d))$. The assertion is that there exists a divisor $D$ on $\bar F_N$ over $\overline{\mathbb Q}$, i.e. a finitely supported integer-valued function on the places of $\bar F_N/\overline{\mathbb Q}$ (valuation subrings containing $\overline{\mathbb Q}$, proper, and principal ideal rings), such that, first, with $\deg D=\sum_v D(v)\deg v$,
--   $$\deg D+1-g=(2m-1)(g-1)+\lfloor m/2\rfloor\,\nu_2+\lfloor 2m/3\rfloor\,\nu_3+(m-1)\,\nu_\infty$$
--   (the floors being natural-number divisions $m/2$ and $2m/3$), and, secondly, every $x$ in the Riemann–Roch space of $D$, that is every $x\in\bar F_N$ whose adic valuation at each place $v$ is at most $\exp(D(v))$, satisfies two integrality conditions: $x^6\,\bar\jmath^{\,4m}(\bar\jmath-1728)^{3m}$ is integral over $\overline{\mathbb Q}[\bar\jmath]$, and $x^{2\psi(N)}\,\bar\jmath^{\,m\psi(N)+1}(\bar\jmath-1728)^{m\psi(N)}$ is integral over $\overline{\mathbb Q}[\bar\jmath^{-1}]$, where $1728$ denotes its image under the structure map $\overline{\mathbb Q}\to\bar F_N$.
--
--   This packages the divisor-theoretic input to the dimension formula for cusp forms of weight $2m$ on $\Gamma_0(N)$: a divisor whose Riemann–Roch defect is exactly the classical dimension expression, together with growth bounds at the places above $j=0$, $j=1728$ and the cusps in the form of integrality over $\overline{\mathbb Q}[\bar\jmath]$ and $\overline{\mathbb Q}[\bar\jmath^{-1}]$. It is used in the proof of [`CuspForm.dimFormula_le_finrank_gamma0`](thm.html#CuspForm.dimFormula_le_finrank_gamma0).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_divisor_degree_weight_and_isIntegral_of_mem_riemannRochSpace.lean

import Mathlib
import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_ModularCurve_GenusNumerics
import Definitions.Def_AlgebraicCurve_RiemannRochRows

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve AlgebraicCurve

theorem ModularCurve.exists_divisor_degree_weight_and_isIntegral_of_mem_riemannRochSpace (N : ℕ) [NeZero N] (m : ℕ) (hm : 1 ≤ m) :
    ∃ D : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N),
      ((D.degree : ℚ) + 1 - ModularCurve.genusFormula N =
        (2 * (m : ℚ) - 1) * (ModularCurve.genusFormula N - 1) + ((m / 2 : ℕ) : ℚ) * (ModularCurve.nuTwo N : ℚ)
          + ((2 * m / 3 : ℕ) : ℚ) * (ModularCurve.nuThree N : ℚ) + ((m : ℚ) - 1) * (ModularCurve.cuspCount N : ℚ)) ∧
      ∀ x : ↥(ModularCurve.modularFunctionFieldBar N), x ∈ AlgebraicCurve.riemannRochSpace D →
        IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) ({ModularCurve.jBar N} : Set ↥(ModularCurve.modularFunctionFieldBar N)))
            (x ^ 6 * ModularCurve.jBar N ^ (4 * m) * (ModularCurve.jBar N - algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) 1728) ^ (3 * m)) ∧
          IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) ({(ModularCurve.jBar N)⁻¹} : Set ↥(ModularCurve.modularFunctionFieldBar N)))
            (x ^ (2 * ModularCurve.dedekindPsi N) * ModularCurve.jBar N ^ (m * ModularCurve.dedekindPsi N + 1) *
              (ModularCurve.jBar N - algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) 1728) ^ (m * ModularCurve.dedekindPsi N)) := by sorry
