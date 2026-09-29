-- Prove2me | Theorems.Thm_ModularCurve_JZero_quot_rep
-- name    : ModularCurve.JZero.quot_rep
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/5f5511f8-17d5-5a5c-9763-391edae75d19
-- title:
--   Quotients of sections of k· E with bounded k
-- statement:
--   Let $N\ge 1$ and let $\bar F_N$ denote `modularFunctionFieldBar N`, the subfield of the Laurent series field over $\overline{\mathbb Q}$ generated over $\overline{\mathbb Q}$ by the coefficientwise image of the field `modularFunctionFieldFull N` (itself generated over $\mathbb Q$ by the divisor expansions attached to $N$). Places of $\bar F_N$ over $\overline{\mathbb Q}$ are valuation subrings containing $\overline{\mathbb Q}$, distinct from the whole field and principal ideal rings; each carries its adic valuation, the induced order function $\operatorname{ord}_v$, and $E = {}$ `embDivisor N` is $(2g+1)$ times the divisor $1\cdot\bar\infty$ supported at the cusp `cuspInftyBar N`, where $g$ is the genus. For a divisor $D$, $L(D) = {}$ `riemannRochSpace D` is the $\overline{\mathbb Q}$-subspace of $f$ with $v(f)\le \exp(D_v)$ for all $v$. Given $r$ and a family $s:\{0,\dots,r-1\}\to\bar F_N$ that is linearly independent over $\overline{\mathbb Q}$ and spans $L(E)$, the assertion is: there is a real constant $C_0$ such that for every nonzero $f\in\bar F_N$, every divisor $A$ with $A_w=\operatorname{ord}_w f$ at every place $w$, and every place $v$ with $A_v=0$ and $v\ne\bar\infty$, there exist $k\in\mathbb N$ and $u_1,u_2\in L(k\cdot E)$ with $k\le \sum_w |A_w|+C_0$, $u_2\ne 0$, $\operatorname{ord}_v u_2=0$ and $f\,u_2=u_1$.
--
--   This is a uniform denominator bound for the projective model of $X_0(N)$ attached to a basis of $L(E)$: every nonzero function is a quotient of two sections of one and the same space $L(k\cdot E)$, with $k$ bounded linearly in the mass $\sum_w|\operatorname{ord}_w f|$ of the divisor of $f$, and with the denominator nonvanishing at a prescribed place $v$ away from the cusp. It feeds the chord-line estimates for the height form on `JZero N`, being cited by [`ModularCurve.JZero.chordLine_core_of_prime_of_five_le`](thm.html#ModularCurve.JZero.chordLine_core_of_prime_of_five_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_quot_rep.lean

import Definitions.Def_ModularCurve_JZeroHeightForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.quot_rep (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ C₀ : ℝ, ∀ (f : modularFunctionFieldBar N)
      (A : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      f ≠ 0 → (∀ w, A w = w.ord f) →
      ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), A v = 0 → v ≠ cuspInftyBar N →
      ∃ (k : ℕ) (u₁ u₂ : modularFunctionFieldBar N),
        (k : ℝ) ≤ (A.sum fun _ m => |(m : ℝ)|) + C₀ ∧
        u₁ ∈ riemannRochSpace ((k : ℤ) • embDivisor N) ∧
        u₂ ∈ riemannRochSpace ((k : ℤ) • embDivisor N) ∧
        u₂ ≠ 0 ∧ v.ord u₂ = 0 ∧ f * u₂ = u₁ := by sorry
