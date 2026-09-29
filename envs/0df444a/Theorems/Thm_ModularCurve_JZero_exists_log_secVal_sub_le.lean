-- Prove2me | Theorems.Thm_ModularCurve_JZero_exists_log_secVal_sub_le
-- name    : ModularCurve.JZero.exists_log_secVal_sub_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/31ae89f6-41cb-5cf3-b33a-999d91bdf5ca
-- title:
--   Upper bound for normalised section values on X₀(N)
-- statement:
--   Let $N \ge 1$ and let $\bar F_N$ denote `modularFunctionFieldBar N`, the base change to $\overline{\mathbb Q}$ of the full level-$N$ modular function field inside Laurent series. Let $E$ be `embDivisor N`, the divisor $(2g+1)\,\bar\infty$ supported at the cusp `cuspInftyBar N`, with $g$ the genus of $\bar F_N$ over $\overline{\mathbb Q}$. Let $s : \mathrm{Fin}\,r \to \bar F_N$ satisfy `IsEmbBasis N s`, that is, $s$ is linearly independent over $\overline{\mathbb Q}$ and its range spans the Riemann–Roch space $L(E) = \{f : v(f) \le \exp(E(v))\ \text{for all places } v\}$. Let $\sigma : \overline{\mathbb Q} \to \mathbb C$ be a ring homomorphism, $k \in \mathbb N$, and $u \in \bar F_N$ nonzero with $u \in L(kE)$. Let $B$ be a divisor on $\bar F_N$ with $B(w) = \mathrm{ord}_w(u) + k\,E(w)$ at every place $w$. Then there is a real number $S$ such that for every place $y$ of $\bar F_N$ over $\overline{\mathbb Q}$ with $B(y) = 0$ one has $$\log\bigl|\sigma(\mathrm{secVal}(s,y,k,u))\bigr| - k\,\log\Bigl(\sup_i \bigl|\sigma(\mathrm{evalVec}(s,y,i))\bigr|\Bigr) \le S,$$ where, with $p$ the pivot index `pivotIndex s y` minimising $\mathrm{ord}_y(s_i)$, $\mathrm{secVal}(s,y,k,u)$ is the residue value at $y$ of $u\,s_p^{-k}$ and $\mathrm{evalVec}(s,y,i)$ is the residue value at $y$ of $s_i s_p^{-1}$ (both set to $0$ when $r = 0$). The bound $S$ may depend on $N$, $s$, $\sigma$, $k$ and $u$.
--
--   This is the upper-bound half of the archimedean pencil estimate on $X_0(N)$: off the support of the effective zero-cycle $B = \mathrm{div}(u) + kE$, the value of $u$ in the pivot trivialisation of degree $k$ is bounded by the $k$-th power of the sup-norm of the projective coordinate vector supplied by a basis of $L(E)$. It feeds the two-sided comparison [`ModularCurve.JZero.pencil_secProd_chowForm_two_sided`](thm.html#ModularCurve.JZero.pencil_secProd_chowForm_two_sided) used in the Chow-form description of heights on the Jacobian.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_exists_log_secVal_sub_le.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_AlgebraicCurve_CycleChowForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.exists_log_secVal_sub_le (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (σ : (AlgebraicClosure ℚ) →+* ℂ) (k : ℕ) (u : modularFunctionFieldBar N) (hu : u ≠ 0)
    (huL : u ∈ riemannRochSpace ((k : ℤ) • embDivisor N))
    (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hB : ∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) :
    ∃ S : ℝ, ∀ y : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), B y = 0 →
      (Real.log ‖σ (secVal s y k u)‖ - (k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s y i)‖)) ≤ S := by sorry
