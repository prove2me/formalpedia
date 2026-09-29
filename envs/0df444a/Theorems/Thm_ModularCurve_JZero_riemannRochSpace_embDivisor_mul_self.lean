-- Prove2me | Theorems.Thm_ModularCurve_JZero_riemannRochSpace_embDivisor_mul_self
-- name    : ModularCurve.JZero.riemannRochSpace_embDivisor_mul_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/8247d3a3-0dcc-5615-9118-d2f5d8f42ed2
-- title:
--   Quadratic normality of L((2g+1)∞̄) on X₀(N)
-- statement:
--   Fix a natural number $N$ with $N \neq 0$, and work with the function field $F_N =$ [`ModularCurve.modularFunctionFieldBar N`](def/ModularCurve_ArithmeticGalois.html#L111), the base change to $\overline{\mathbb Q}$ of the full modular function field of level $N$ inside the field of Laurent series over $\overline{\mathbb Q}$, regarded as an extension of $K = \overline{\mathbb Q}$. Let $g =$ [`AlgebraicCurve.genusFF`](def/AlgebraicCurve_Repartitions.html#L145) $K\, F_N$ and put $E =$ [`ModularCurve.embDivisor N`](def/ModularCurve_JZeroHeightForm.html#L106), the divisor $(2g+1)\cdot[\bar\infty]$, i.e. $(2g+1)$ times the `Finsupp`-basis divisor concentrated at the place [`ModularCurve.cuspInftyBar N`](def/ModularCurve_AtkinLehner.html#L93) of $F_N$. For a divisor $D$ on $F_N$, [`AlgebraicCurve.riemannRochSpace D`](def/AlgebraicCurve_Repartitions.html#L105) is the $K$-submodule of $F_N$ consisting of those $f$ with $v(f) \le \exp(D(v))$ for every place $v$, the valuations being the $\mathbb Z^{m0}$-valued adic valuations attached to the places; thus it is the space of functions whose pole order at each $v$ is bounded by the multiplicity $D(v)$. The assertion is the equality of $K$-submodules of $F_N$
--   $$\mathrm{L}(E)\cdot \mathrm{L}(E) = \mathrm{L}(2\cdot E),$$
--   where the left-hand side is the submodule product, that is the $K$-span of all products $fh$ with $f,h \in \mathrm{L}(E)$, and on the right $2 \cdot E$ is the integer multiple $(4g+2)\cdot[\bar\infty]$. Concretely: every element of $F_N$ which is regular away from $\bar\infty$ and has a pole of order at most $4g+2$ there is a $\overline{\mathbb Q}$-linear combination of products of two functions each with pole order at most $2g+1$ at $\bar\infty$ and no other poles.
--
--   This is the degree-two step of projective normality (in the sense of Castelnuovo and Mumford) for the complete linear system of the divisor $(2g+1)\bar\infty$ of degree $2g+1$ on $X_0(N)$ over $\overline{\mathbb Q}$; combined with the corresponding statements $\mathrm{L}(E)\cdot\mathrm{L}(kE)=\mathrm{L}((k+1)E)$ for $k \ge 2$ it gives surjectivity of $\operatorname{Sym}^m \mathrm{L}(E) \to \mathrm{L}(mE)$ for all $m$. It is used in the analysis of the height form and of monomial spans on $J_0(N)$, for instance by [`ModularCurve.JZero.exists_isHomogeneous_aeval_eq_zero_and_eval_ne_zero`](thm.html#ModularCurve.JZero.exists_isHomogeneous_aeval_eq_zero_and_eval_ne_zero) and [`ModularCurve.JZero.exists_sum_pairHt_le_of_det_evalAt_ne_zero`](thm.html#ModularCurve.JZero.exists_sum_pairHt_le_of_det_evalAt_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_riemannRochSpace_embDivisor_mul_self.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroHeightForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.JZero.riemannRochSpace_embDivisor_mul_self (N : ℕ) [NeZero N] :
    AlgebraicCurve.riemannRochSpace (ModularCurve.embDivisor N)
        * AlgebraicCurve.riemannRochSpace (ModularCurve.embDivisor N)
      = AlgebraicCurve.riemannRochSpace ((2 : ℤ) • ModularCurve.embDivisor N) := by sorry
