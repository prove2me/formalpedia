-- Prove2me | Theorems.Thm_ModularCurve_JZero_exists_one_le_abv_evalAt_of_le_prox
-- name    : ModularCurve.JZero.exists_one_le_abv_evalAt_of_le_prox
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/1d16b1eb-0587-5b95-8534-7109dfc2b488
-- title:
--   A function is large at places chordally near one of its poles
-- statement:
--   Fix $N\ge 1$ and let $\overline F_N$ denote `modularFunctionFieldBar N`, the subfield of $\overline{\mathbb Q}((t))$ generated over $\overline{\mathbb Q}$ by the coefficientwise image of the field `modularFunctionFieldFull N` (itself generated over $\mathbb Q$ by the divisor expansions attached to level $N$). Let $s=(s_i)_{i<r}$ be a family in $\overline F_N$ satisfying `IsEmbBasis N s`, i.e. $s$ is linearly independent over $\overline{\mathbb Q}$ and spans the Riemann–Roch space $\{f : \nu_v(f)\le \exp(D(v))$ for all places $v\}$ of the divisor $D=$ `embDivisor N`, a fixed positive multiple of the cusp $\overline\infty$. Let $h\in\overline F_N$, and let $Q$ be a place of $\overline F_N$ over $\overline{\mathbb Q}$ (a proper valuation subring containing $\overline{\mathbb Q}$ whose ring is a principal ideal ring) with $\mathrm{ord}_Q(h)<0$, and let $p$ be a prime. Then there is a real $c\ge 0$ with the following property: for every non-archimedean absolute value $\mu$ on $\overline{\mathbb Q}$ with $\mu(p)<1$ and every place $R$ of $\overline F_N$ with $\mathrm{ord}_R(h)=0$, if $$c\,\bigl(-\log\mu(p)\bigr)\;\le\;\log\sup_i\mu(x_i)+\log\sup_j\mu(y_j)-\log\sup_{i,j}\mu(x_iy_j-x_jy_i),$$ where $x=$ `evalVec s R` and $y=$ `evalVec s Q` are the coordinate rows $x_i=R.\mathrm{evalAt}(s_i s_{i_R}^{-1})$, $y_i=Q.\mathrm{evalAt}(s_i s_{i_Q}^{-1})$ normalised at the pivot indices minimising $\mathrm{ord}$ (and zero when $r=0$), then $1\le\mu\bigl(R.\mathrm{evalAt}(h)\bigr)$. Here $v.\mathrm{evalAt}(f)$ is the residue of $f$ at $v$ pulled back to $\overline{\mathbb Q}$ when $f$ lies in the valuation subring, and $0$ otherwise.
--
--   This is the local assertion that a function is large in absolute value at all places lying in a sufficiently small chordal ball around a fixed pole $Q$, with radius $e^{-cL}$, $L=-\log\mu(p)$, and with a constant depending only on $s$, $h$, $Q$ and $p$ — in particular uniformly in the non-archimedean absolute value $\mu$ extending the $p$-adic one. It feeds the proximity-versus-height estimates on $J_0(N)$ through [`ModularCurve.exists_log_absValue_evalAt_ge_of_forall_prox_le`](thm.html#ModularCurve.exists_log_absValue_evalAt_ge_of_forall_prox_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_exists_one_le_abv_evalAt_of_le_prox.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.exists_one_le_abv_evalAt_of_le_prox (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (h : modularFunctionFieldBar N)
    (Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hQ : Q.ord h < 0) (p : ℕ) (hp : p.Prime) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
      μ (p : AlgebraicClosure ℚ) < 1 →
      ∀ R : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), R.ord h = 0 →
        c * (-Real.log (μ (p : AlgebraicClosure ℚ))) ≤ prox μ (evalVec s R) (evalVec s Q) →
        1 ≤ μ (R.evalAt h) := by sorry
